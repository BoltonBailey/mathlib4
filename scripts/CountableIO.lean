/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib

/-!
# Detecting functions with countable input and output types

A function `f : (x₁ : A₁) → (x₂ : A₂ x₁) → ⋯ → B x₁ ⋯ xₙ` is, after uncurrying, a function
`f' : (Σ x₁, Σ x₂, ⋯ Aₙ) → B`. A necessary condition for `f` to be computable by a Turing
machine (in the classical sense, on encoded inputs/outputs) is that both this dependent sum and
`B` are countable. This file checks that condition.

## Scope: monomorphic functions only

Declarations with a *type parameter*, i.e. an argument whose type is a universe or a type
family (`{α : Type u}`, `{β : α → Type v}`, `(motive : ℕ → Sort u)`), are ignored: they are
reported as `ignored` by `#countable_io` and skipped by `#countable_io_scan`.

## Method

We walk the telescope of the declaration's type one binder at a time, adding each argument as a
free variable, and try to show `Countable Aᵢ` *in the context of the earlier arguments* (and of
any earlier instance arguments, which become local instances). If this succeeds for every `i`,
it proves `∀ x₁ ⋯ xᵢ₋₁, Countable (Aᵢ x₁ ⋯)`, so the iterated `Σ`-type is countable by
`instCountableSigma`. The output type is checked the same way.

A type is shown countable either
* by synthesizing a `Countable` instance, or
* if it is a Π-type, by grouping each data binder with the propositional binders that follow
  it: `(y : A) → (h₁ : P₁ y) → (h₂ : P₂ y h₁) → ⋯ → R` is equivalent to `(v : D) → R` with
  `D = {y // ∃ h₁, ∃ h₂, ⋯}`. This is countable if `D` is finite and `R` is (recursively) shown
  countable in the context of `y, h₁, …`. For finiteness of `D` it suffices that `A` is
  `Finite`, or that `{y // Pⱼ y}` is `Finite` for some hypothesis `Pⱼ` mentioning only `y`
  (since `D` embeds into it).
  A binder over a proposition alone, `(h : P) → R`, has a subsingleton domain and only needs `R`
  countable. This handles e.g. `(i : ℕ) → i < n → Bool`, where `Countable` instances fail
  because the outer domain `ℕ` is infinite.

So a `countable` verdict is backed by actual instances and is never wrong; it is an
under-approximation limited by the coverage of `Countable`/`Finite` instances in Mathlib.

For each type we report one of
* `countable`: shown countable as above;
* `uncountable`: the type is a universe `Type u` / `Sort u` (uncountable since it surjects onto
  `Cardinal`; for `Sort u` this means "for some `u`"), a type family `D → Type u` with `D`
  nonempty, a function space `α → β` with `α` infinite and `β` nontrivial, a `Set α` with `α`
  infinite, or an `Uncountable` instance was synthesized;
* `unknown`: none of the above.

The input is `uncountable` when some argument is (strictly speaking the `Σ`-type could still be
countable if a *later* argument is empty for all but countably many values, e.g. a hypothesis
`(h : False)`; this is rare).

## Usage

```
#countable_io Nat.gcd               -- per-argument report
#countable_io_scan "out.tsv"        -- scan the whole environment, write a TSV file
#countable_io_scan "out.tsv" Nat    -- only declarations under the namespace `Nat`
#countable_io_scan_modules "out.tsv" Mathlib  -- incremental, resumable, module by module
```
Run from the repository root with `lake env lean scripts/CountableIO.lean`, or use
`scripts/countable_io_scan.sh` for the incremental module-by-module scan.
-/

open Lean Meta Elab Command

namespace CountableIO

/-- Verdict on the cardinality of a single type. -/
inductive Verdict where
  | countable
  | uncountable
  | unknown
  deriving Repr, BEq, Inhabited

instance : ToString Verdict where
  toString
    | .countable => "countable"
    | .uncountable => "uncountable"
    | .unknown => "unknown"

/-- Configuration for the analysis. -/
structure Config where
  /-- Heartbeat budget (in thousands) for each instance synthesis problem. -/
  synthHeartbeats : Nat := 20000
  /-- Heartbeat budget (in thousands) for analyzing one declaration during a scan. -/
  declHeartbeats : Nat := 400000

/-- Report on one argument (or the output) of a function. -/
structure TypeReport where
  name : Name
  binderInfo : BinderInfo := .default
  /-- The pretty-printed type, in the context of the previous arguments. -/
  type : String
  verdict : Verdict
  reason : String
  deriving Inhabited

/-- Report on a whole declaration. -/
structure Report where
  decl : Name
  /-- The first type parameter, if any; the declaration is then ignored. -/
  typeParam? : Option TypeReport
  args : Array TypeReport
  output : TypeReport
  deriving Inhabited

/-- Verdict for the uncurried input `Σ x₁, ⋯, Aₙ`. -/
def Report.inputVerdict (r : Report) : Verdict :=
  let vs := r.args.map (·.verdict)
  if vs.all (· == .countable) then .countable
  else if vs.any (· == .uncountable) then .uncountable
  else .unknown

/-- Whether both the uncurried input and the output were shown to be countable. -/
def Report.isCountableIO (r : Report) : Bool :=
  r.inputVerdict == .countable && r.output.verdict == .countable

/-- The first input argument that is not known to be countable, if any. -/
def Report.firstBlocker? (r : Report) : Option TypeReport :=
  r.args.find? (·.verdict != .countable)

/-- If `T` is (up to reducible unfolding) of the form `∀ ys, Sort u` with `u` not
definitionally `0`, return the number of binders `ys`. This detects universes (`0` binders)
and type families. Predicates `α → Prop` are deliberately *not* detected. -/
def typeFamilyArity? (T : Expr) : MetaM (Option Nat) :=
  withReducible <| forallTelescopeReducing T fun ys b => do
    match b with
    | .sort u => return if u.normalize.isZero then none else some ys.size
    | _ => return none

/-- Try to synthesize `cls T`, with a heartbeat budget; never throws. -/
def trySynth (cfg : Config) (cls : Name) (T : Expr) : MetaM Bool := do
  tryCatchRuntimeEx
    (withTheReader Core.Context
      (fun ctx => { ctx with maxHeartbeats := cfg.synthHeartbeats * 1000 }) <|
      withCurrHeartbeats do
        let goal ← mkAppM cls #[T]
        return (← synthInstance? goal).isSome)
    fun _ => return false

/-- Whether the domain of a telescope `∀ (y₁ : D₁) (y₂ : D₂ y₁) ⋯, _` is provably nonempty, i.e.
each `Dᵢ` has a `Nonempty` instance in the context of the previous binders. -/
def telescopeDomainNonempty (cfg : Config) (T : Expr) : MetaM Bool :=
  withReducible <| forallTelescopeReducing T fun ys _ =>
    ys.allM fun y => do trySynth cfg ``Nonempty (← inferType y)

/-- Introduce the leading propositional binders of `T` as local hypotheses and pass them,
together with the remaining type, to `k`. -/
partial def withPropBinders {α} (T : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
  go T #[]
where
  go (T : Expr) (hs : Array Expr) : MetaM α := do
    if let .forallE n d b bi := ← whnfR T then
      if ← isProp d then
        return ← withLocalDecl n bi d fun h => go (b.instantiate1 h) (hs.push h)
    k hs T

mutual

/-- Classify the cardinality of a type `T` in the current local context. -/
partial def classify (cfg : Config) (T : Expr) : MetaM (Verdict × String) := do
  match ← typeFamilyArity? T with
  | some 0 => return (.uncountable, "universe")
  | some _ =>
    -- `D → Type u` contains the constant families, so it is uncountable if `D` is nonempty.
    if ← telescopeDomainNonempty cfg T then
      return (.uncountable, "type family over a nonempty domain")
    return (.unknown, "type family")
  | none =>
    if ← trySynth cfg ``Countable T then return (.countable, "Countable instance")
    if ← trySynth cfg ``Uncountable T then return (.uncountable, "Uncountable instance")
    if ← piCountable cfg T then
      return (.countable, "Π-type over finite (sub)domains with countable codomain")
    -- A non-dependent function space `α → β` (e.g. `α → Prop`) with `α` infinite and
    -- `β` nontrivial has cardinality at least `2 ^ ℵ₀`.
    if let .forallE _ a b _ := ← whnfD T then
      if !b.hasLooseBVars then
        if (← trySynth cfg ``Infinite a) && (← trySynth cfg ``Nontrivial b) then
          return (.uncountable, "functions from an infinite to a nontrivial type")
    -- `Set α` (a structure wrapping `α → Prop`) is uncountable when `α` is infinite.
    if let some a := (← whnfR T).app1? ``Set then
      if ← trySynth cfg ``Infinite a then
        return (.uncountable, "Set of an infinite type")
    return (.unknown, "no Countable instance found")

/-- Show that a Π-type `(y : A) → (h₁ : P₁ y) → (h₂ : P₂ y h₁) → ⋯ → R` is countable.

It is equivalent to `(v : D) → R` where `D = {y // ∃ h₁, ∃ h₂, ⋯}` is the set of `y` for which
all hypotheses can hold. `D` embeds into `{y // Pⱼ y}` for every hypothesis `Pⱼ` that depends
only on `y`, so it suffices that one such subtype is `Finite` (or that `A` is `Finite`), and
that `R` is countable for all values of the binders, which we check recursively.
A leading propositional binder `(h : P) → R` has a subsingleton domain, so we only check `R`.
Returns `false` if this does not succeed. -/
partial def piCountable (cfg : Config) (T : Expr) : MetaM Bool := do
  let .forallE n a b bi := ← whnfR T | return false
  if ← isProp a then
    return ← withLocalDecl n bi a fun h => do
      return (← classify cfg (b.instantiate1 h)).1 == .countable
  withLocalDecl n bi a fun y => do
    withPropBinders (b.instantiate1 y) fun hs rest => do
      let domainFinite ← (do
        if ← trySynth cfg ``Finite a then return true
        for h in hs do
          let p ← inferType h
          if hs.any fun h' => p.containsFVar h'.fvarId! then continue
          if ← trySynth cfg ``Finite (← mkAppM ``Subtype #[← mkLambdaFVars #[y] p]) then
            return true
        return false)
      unless domainFinite do return false
      return (← classify cfg rest).1 == .countable

end

/-- Analyze a (closed) function type. -/
partial def analyzeType (cfg : Config) (declName : Name) (type : Expr) : MetaM Report :=
  go type none #[]
where
  go (type : Expr) (typeParam? : Option TypeReport) (args : Array TypeReport) :
      MetaM Report := do
    match ← whnfR type with
    | .forallE n d b bi =>
      let n := n.eraseMacroScopes
      let tyStr := toString (← ppExpr d)
      let isTypeParam := (← typeFamilyArity? d).isSome
      withLocalDecl n bi d fun x => do
        let (v, reason) ← classify cfg d
        let r : TypeReport := { name := n, binderInfo := bi, type := tyStr, verdict := v, reason }
        let typeParam? := if typeParam?.isNone && isTypeParam then some r else typeParam?
        go (b.instantiate1 x) typeParam? (args.push r)
    | _ =>
      let (v, reason) ← classify cfg type
      return { decl := declName, typeParam?, args,
               output := { name := `output, type := toString (← ppExpr type), verdict := v,
                           reason } }

/-- Analyze the declaration `declName`. -/
def analyzeDecl (cfg : Config) (declName : Name) : MetaM Report := do
  analyzeType cfg declName (← getConstInfo declName).type

/-- Whether the type `type` has an argument that is a type parameter (a universe or a type
family). This is a cheap pre-check that avoids running instance synthesis. -/
def hasTypeParam (type : Expr) : MetaM Bool :=
  withReducible <| forallTelescopeReducing type fun xs _ =>
    xs.anyM fun x => return (← typeFamilyArity? (← inferType x)).isSome

/-- Should `declName` be considered a "function" for the purposes of a scan? We keep
definitions, opaque constants and constructors, and drop theorems (and Prop-valued
definitions, i.e. proofs), instances, and auxiliary/internal declarations. -/
def isCandidate (declName : Name) (info : ConstantInfo) : MetaM Bool := do
  unless info matches .defnInfo _ | .opaqueInfo _ | .ctorInfo _ do return false
  if ← declName.isBlackListed then return false
  if ← isInstance declName then return false
  try
    return !(← isProp info.type)
  catch _ => return false

/-- Pretty-print a report. -/
def Report.toMessageData (r : Report) : MessageData :=
  let line (t : TypeReport) : MessageData :=
    let mark := match t.verdict with
      | .countable => "✓" | .uncountable => "✗" | .unknown => "?"
    m!"  {mark} {t.name} : {t.type}  — {t.verdict} ({t.reason})"
  let header := match r.typeParam? with
    | some t => m!"{r.decl}: IGNORED (type parameter {t.name} : {t.type})"
    | none => m!"{r.decl}: input {r.inputVerdict}, output {r.output.verdict}" ++
      (if r.isCountableIO then m!" ⇒ COUNTABLE I/O" else m!"")
  let lines := r.args.toList.map line ++ [line r.output]
  lines.foldl (fun acc l => acc ++ "\n" ++ l) header

/-- Escape a field for TSV output. -/
private def tsvEscape (s : String) : String :=
  s.map fun c => if c == '\t' || c == '\n' then ' ' else c

/-- Kind of a constant, for the TSV output. -/
private def kindString : ConstantInfo → String
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .ctorInfo _ => "ctor"
  | _ => "other"

/-- Header of the TSV output. -/
def tsvHeader : String := "name\tmodule\tkind\tcountable_io\tinput\toutput\tblocker"

/-- Outcome of scanning one declaration. -/
inductive ScanResult where
  /-- Not a function (theorem, instance, auxiliary declaration, …). -/
  | notCandidate
  /-- Ignored because it has a type parameter. -/
  | typeParam
  /-- A TSV row, and whether the declaration has countable I/O. -/
  | row (countableIO : Bool) (line : String)

/-- Scan one declaration, with a fresh heartbeat budget of `cfg.declHeartbeats` (in thousands).
If the analysis throws or runs out of heartbeats, we emit a row with verdict `error`. -/
def scanDecl (cfg : Config) (modName : Name) (n : Name) (info : ConstantInfo) :
    MetaM ScanResult := do
  let mkRow (fields : List String) : String :=
    "\t".intercalate <| ([toString n, toString modName, kindString info] ++ fields).map tsvEscape
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := cfg.declHeartbeats * 1000 })
      <| withCurrHeartbeats do
        unless ← isCandidate n info do return .notCandidate
        if ← hasTypeParam info.type then return .typeParam
        let r ← analyzeDecl cfg n
        let blocker := match r.firstBlocker? with
          | some t => s!"{t.name} : {t.type}"
          | none => if r.output.verdict == .countable then "" else s!"output : {r.output.type}"
        return .row r.isCountableIO <| mkRow [toString r.isCountableIO, toString r.inputVerdict,
          toString r.output.verdict, blocker])
    fun e => do
      return .row false <| mkRow ["error", "", "", String.ofList ((← e.toMessageData.toString).toList.take 200)]

/-- Running totals of a scan: analyzed, countable-I/O, skipped for a type parameter. -/
structure ScanStats where
  analyzed : Nat := 0
  countable : Nat := 0
  skipped : Nat := 0

/-- Scan the declarations `names` (defined in module `modName`), returning the TSV rows. -/
def scanNames (cfg : Config) (modName : Name) (names : Array Name) (stats : ScanStats) :
    MetaM (Array String × ScanStats) := do
  let env ← getEnv
  let mut stats := stats
  let mut rows := #[]
  for n in names.qsort Name.lt do
    let some info := env.find? n | continue
    match ← scanDecl cfg modName n info with
    | .notCandidate => pure ()
    | .typeParam => stats := { stats with skipped := stats.skipped + 1 }
    | .row c line =>
      rows := rows.push line
      stats := { stats with analyzed := stats.analyzed + 1,
                            countable := stats.countable + if c then 1 else 0 }
  return (rows, stats)

/-- The module in which `n` is defined, or `anonymous` for the current file. -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

/-- One-shot scan of all declarations whose name satisfies `p`, writing a TSV file at the end. -/
def scan (path : System.FilePath) (p : Name → Bool) (cfg : Config := {}) : MetaM ScanStats := do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n _ => if p n then acc.push n else acc
  let mut stats : ScanStats := {}
  let mut rows := #[tsvHeader]
  for n in names.qsort Name.lt do
    let (rs, s) ← scanNames cfg (moduleOf env n) #[n] stats
    rows := rows ++ rs
    stats := s
  IO.FS.writeFile path ("\n".intercalate rows.toList ++ "\n")
  return stats

/-- Incremental, resumable scan of all modules whose name starts with `modPrefix`, module by
module, in import order. After each module, its rows are appended to `out` and the module name
is appended to `out.done`; on restart, modules listed in `out.done` are skipped. -/
def scanModules (out : System.FilePath) (modPrefix : Name) (cfg : Config := {}) :
    MetaM ScanStats := do
  let env ← getEnv
  let mods := env.header.moduleNames
  let byMod := env.constants.fold (init := Array.replicate mods.size (#[] : Array Name))
    fun acc n _ => match env.getModuleIdxFor? n with
      | some i => acc.modify i.toNat (·.push n)
      | none => acc
  let donePath : System.FilePath := out.toString ++ ".done"
  let done : Std.HashSet String ←
    if ← donePath.pathExists then
      pure <| Std.HashSet.ofArray (← IO.FS.lines donePath)
    else pure {}
  unless ← out.pathExists do IO.FS.writeFile out (tsvHeader ++ "\n")
  let outH ← IO.FS.Handle.mk out .append
  let doneH ← IO.FS.Handle.mk donePath .append
  let todo := (Array.range mods.size).filter fun i =>
    modPrefix.isPrefixOf mods[i]! && !done.contains (toString mods[i]!)
  IO.eprintln s!"countable_io: {todo.size} modules to scan ({done.size} already done)"
  let mut stats : ScanStats := {}
  let mut k := 0
  for i in todo do
    let m := mods[i]!
    -- Keep memory bounded: drop Meta caches between modules.
    modifyThe Meta.State fun s => { s with cache := {} }
    let (rows, s) ← scanNames cfg m byMod[i]! stats
    stats := s
    outH.putStr (String.join (rows.toList.map (· ++ "\n")))
    outH.flush
    doneH.putStrLn (toString m)
    doneH.flush
    k := k + 1
    if k % 100 == 0 || k == todo.size then
      IO.eprintln s!"countable_io: {k}/{todo.size} modules, {stats.analyzed} analyzed, \
        {stats.countable} countable-I/O, {stats.skipped} skipped (type parameter)"
  return stats

/-- Summary message for a scan. -/
def ScanStats.toMessageData (s : ScanStats) (path : String) : MessageData :=
  m!"Analyzed {s.analyzed} functions without type parameters ({s.skipped} skipped for having \
    one): {s.countable} have countable I/O. Results in {path}."

/-- `#countable_io f` reports, argument by argument, whether `f` has countable input and output
types when uncurried. Declarations with a type parameter are reported as ignored. -/
elab "#countable_io " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  logInfo (← analyzeDecl {} n).toMessageData

/-- `#countable_io_scan "file.tsv"` analyzes every function in the environment without type
parameters and writes the results to `file.tsv`. `#countable_io_scan "file.tsv" Foo` restricts
to declarations in namespace `Foo`. -/
elab "#countable_io_scan " path:str ns:(ppSpace ident)? : command => liftTermElabM do
  let p : Name → Bool := match ns with
    | some ns => fun n => ns.getId.isPrefixOf n
    | none => fun _ => true
  logInfo ((← scan path.getString p).toMessageData path.getString)

/-- `#countable_io_scan_modules "file.tsv" Mathlib` scans, module by module, every module whose
name starts with `Mathlib`, appending results to `file.tsv` as it goes. It is resumable: modules
already listed in `file.tsv.done` are skipped. -/
elab "#countable_io_scan_modules " path:str mod:ident : command => liftTermElabM do
  logInfo ((← scanModules path.getString mod.getId).toMessageData path.getString)

end CountableIO
