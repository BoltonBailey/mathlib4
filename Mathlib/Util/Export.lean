/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Init
public meta import Lean.CoreM
public meta import Lean.Util.FoldConsts

/-!
# A rudimentary export format

Adapted from
<https://github.com/leanprover-community/lean/blob/master/doc/export_format.md>
with support for Lean 4 kernel primitives.
-/

public meta section

open Lean
open Std (HashMap HashSet)

namespace Lean

namespace Export

/-! References -/

private opaque MethodsRefPointed : NonemptyType.{0}

private def MethodsRef : Type := MethodsRefPointed.type

/-- The kinds of object the exporter assigns an index to and emits: names, universe levels,
expressions and definitions. Indices are shared across a single export, so an entry emitted once
may be referred to from anywhere later in the file. -/
inductive Entry
  | name (n : Name)
  | level (n : Level)
  | expr (n : Expr)
  | defn (n : Name)
deriving Inhabited

instance : Coe Name Entry := ⟨Entry.name⟩
instance : Coe Level Entry := ⟨Entry.level⟩
instance : Coe Expr Entry := ⟨Entry.expr⟩

/-- An index allocator for objects of type `α`, recording the index already given to each object
together with the next index to hand out. -/
structure Alloc (α) [BEq α] [Hashable α] where
  /-- The index assigned to each object exported so far. -/
  map : Std.HashMap α Nat
  /-- The next unused index. -/
  next : Nat
deriving Inhabited

/-- The exporter's state: one index allocator per kind of object, the set of declarations already
emitted, and a stack of pending entries. -/
structure State where
  /-- Indices assigned to names. -/
  names : Alloc Name := ⟨(∅ : Std.HashMap Name Nat).insert Name.anonymous 0, 1⟩
  /-- Indices assigned to universe levels. -/
  levels : Alloc Level := ⟨(∅ : Std.HashMap Level Nat).insert .zero 0, 1⟩
  /-- Indices assigned to expressions. -/
  exprs : Alloc Expr
  /-- The declarations that have already been emitted. -/
  defs : Std.HashSet Name
  /-- A stack of entries paired with a visited flag, for a non-recursive traversal. Unused by the
  current exporter, which recurses directly. -/
  stk : Array (Bool × Entry)
deriving Inhabited

/-- Uniform access to the `Alloc α` field of the state, so that `alloc` can be written once and used
for names, levels and expressions alike. -/
class OfState (α : Type) [BEq α] [Hashable α] where
  /-- Project the allocator for `α` out of the state. -/
  get : State → Alloc α
  /-- Update the allocator for `α` inside the state. -/
  modify : (Alloc α → Alloc α) → State → State

instance : OfState Name where
  get s := s.names
  modify f s := { s with names := f s.names }

instance : OfState Level where
  get s := s.levels
  modify f s := { s with levels := f s.levels }

instance : OfState Expr where
  get s := s.exprs
  modify f s := { s with exprs := f s.exprs }

end Export

/-- The exporter monad: `CoreM` carrying the exporter's `State`. -/
abbrev ExportM := StateT Export.State CoreM

namespace Export

/-- Assign the next free index to `a`, recording it in the state, and return that index. The caller
is responsible for actually emitting the line that defines the object at that index. -/
def alloc {α} [BEq α] [Hashable α] [OfState α] (a : α) : ExportM Nat := do
  let n := (OfState.get (α := α) (← get)).next
  modify <| OfState.modify (α := α) fun s ↦ {map := s.map.insert a n, next := n + 1}
  pure n

/-- Emit `n` and all of its prefixes, returning the index assigned to `n`. Names already exported
are served from the state instead of being emitted twice. The anonymous name is always index
`0`; other names are emitted as `#NS` (string component) or `#NI` (numeric component) applied to
the index of their prefix. -/
def exportName (n : Name) : ExportM Nat := do
  match (← get).names.map[n]? with
  | some i => pure i
  | none => match n with
    | .anonymous => pure 0
    | .num p a => let i ← alloc n; IO.println s!"{i} #NI {← exportName p} {a}"; pure i
    | .str p s => let i ← alloc n; IO.println s!"{i} #NS {← exportName p} {s}"; pure i

/-- Emit the universe level `L` and its subterms, returning the index assigned to `L`. Level `0` is
always index `0`; the other constructors are emitted as `#US` (successor), `#UM` (max), `#UIM`
(impredicative max) and `#UP` (parameter). Universe metavariables cannot appear in an exported
level. -/
def exportLevel (L : Level) : ExportM Nat := do
  match (← get).levels.map[L]? with
  | some i => pure i
  | none => match L with
    | .zero => pure 0
    | .succ l =>
      let i ← alloc L; IO.println s!"{i} #US {← exportLevel l}"; pure i
    | .max l₁ l₂ =>
      let i ← alloc L; IO.println s!"{i} #UM {← exportLevel l₁} {← exportLevel l₂}"; pure i
    | .imax l₁ l₂ =>
      let i ← alloc L; IO.println s!"{i} #UIM {← exportLevel l₁} {← exportLevel l₂}"; pure i
    | .param n =>
      let i ← alloc L; IO.println s!"{i} #UP {← exportName n}"; pure i
    | .mvar _ => unreachable!

/-- The export format's code for a binder annotation. -/
def biStr : BinderInfo → String
  | BinderInfo.default        => "#BD"
  | BinderInfo.implicit       => "#BI"
  | BinderInfo.strictImplicit => "#BS"
  | BinderInfo.instImplicit   => "#BC"

open ConstantInfo in
mutual

/-- Emit the expression `E`, its subterms and the declarations of any constants it mentions,
returning the index assigned to `E`.

Each constructor gets its own line, referring to its subterms by index: `#EV` for a bound
variable, `#ES` for a sort, `#EC` for a constant together with its universe arguments, `#EA` for
an application, `#EL` for a lambda, `#EP` for a pi, `#EN` and `#ET` for natural number and
string literals, and `#EJ` for a projection. Binders also record their binder annotation via
`biStr`.

Free variables, metavariables and `mdata` cannot appear in an exported term, and meeting one is
a bug rather than a user error. -/
partial def exportExpr (E : Expr) : ExportM Nat := do
  match (← get).exprs.map[E]? with
  | some i => pure i
  | none => match E with
    | .bvar n => let i ← alloc E; IO.println s!"{i} #EV {n}"; pure i
    | .fvar _ => unreachable!
    | .mvar _ => unreachable!
    | .sort l => let i ← alloc E; IO.println s!"{i} #ES {← exportLevel l}"; pure i
    | .const n ls =>
      exportDef n
      let i ← alloc E
      let mut s := s!"{i} #EC {← exportName n}"
      for l in ls do s := s ++ s!" {← exportLevel l}"
      IO.println s; pure i
    | .app e₁ e₂ =>
      let i ← alloc E; IO.println s!"{i} #EA {← exportExpr e₁} {← exportExpr e₂}"; pure i
    | .lam _ e₁ e₂ d =>
      let i ← alloc E
      IO.println s!"{i} #EL {biStr d} {← exportExpr e₁} {← exportExpr e₂}"; pure i
    | .forallE _ e₁ e₂ d =>
      let i ← alloc E
      IO.println s!"{i} #EP {biStr d} {← exportExpr e₁} {← exportExpr e₂}"; pure i
    | .letE _ e₁ e₂ e₃ _ =>
      let i ← alloc E
      IO.println s!"{i} #EP {← exportExpr e₁} {← exportExpr e₂} {← exportExpr e₃}"; pure i
    | .lit (.natVal n) => let i ← alloc E; IO.println s!"{i} #EN {n}"; pure i
    | .lit (.strVal s) => let i ← alloc E; IO.println s!"{i} #ET {s}"; pure i
    | .mdata _ _ => unreachable!
    | .proj n k e =>
      let i ← alloc E; IO.println s!"{i} #EJ {← exportName n} {k} {← exportExpr e}"; pure i

/-- Emit the declaration `n`, first emitting every constant that its type or value depends on, and
record it in `State.defs` so that it is never emitted twice.

The line emitted depends on the kind of declaration: `#AX` for an axiom, `#DEF` for a
definition, `#THM` for a theorem, `#CN` for an opaque constant, `#QUOT` for the quotient
primitives, and `#IND` for an inductive type, or `#MUT` for a mutually inductive family. Each of
these is followed by the indices of the name, the type and, where there is one, the value, then
by the indices of the universe parameters.

An inductive line additionally carries the number of parameters, and, for each type in the
family, its name, its type and its constructors with their types; the type itself and its
recursors are marked as emitted at the same time, since the importer reconstructs them from the
inductive declaration rather than reading them separately. -/
partial def exportDef (n : Name) : ExportM Unit := do
  if (← get).defs.contains n then return
  let ci ← getConstInfo n
  for c in ci.value!.getUsedConstants do
    unless (← get).defs.contains c do
      exportDef c
  match ci with
  | axiomInfo   val => axdef "#AX" val.name val.type val.levelParams
  | defnInfo    val => defn "#DEF" val.name val.type val.value val.levelParams
  | thmInfo     val => defn "#THM" val.name val.type val.value val.levelParams
  | opaqueInfo  val => defn "#CN" val.name val.type val.value val.levelParams
  | quotInfo    _ =>
    IO.println "#QUOT"
    for n in [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
      insert n
  | inductInfo  val => ind val.all
  | ctorInfo    val => ind (← getConstInfoInduct val.induct).all
  | recInfo     val => ind val.all
where
  insert (n : Name) : ExportM Unit :=
    modify fun s ↦ { s with defs := s.defs.insert n }
  defn (ty : String) (n : Name) (t e : Expr) (ls : List Name) : ExportM Unit := do
    let mut s := s!"{ty} {← exportName n} {← exportExpr t} {← exportExpr e}"
    for l in ls do s := s ++ s!" {← exportName l}"
    IO.println s
    insert n
  axdef (ty : String) (n : Name) (t : Expr) (ls : List Name) : ExportM Unit := do
    let mut s := s!"{ty} {← exportName n} {← exportExpr t}"
    for l in ls do s := s ++ s!" {← exportName l}"
    IO.println s
    insert n
  ind : List Name → ExportM Unit
  | [] => unreachable!
  | is@(i::_) => do
    let val ← getConstInfoInduct i
    let mut s := match is.length with
    | 1 => s!"#IND {val.numParams}"
    | n => s!"#MUT {val.numParams} {n}"
    for j in is do insert j; insert (mkRecName j)
    for j in is do
      let val ← getConstInfoInduct j
      s := s ++ s!" {← exportName val.name} {← exportExpr val.type} {val.ctors.length}"
      for c in val.ctors do
        insert c
        s := s ++ s!" {← exportName c} {← exportExpr (← getConstInfoCtor c).type}"
    for j in is do s ← indbody j s
    for l in val.levelParams do s := s ++ s!" {← exportName l}"
    IO.println s
  indbody (ind : Name) (s : String) : ExportM String := do
    let val ← getConstInfoInduct ind
    let mut s := s ++ s!" {← exportName ind} {← exportExpr val.type} {val.ctors.length}"
    for c in val.ctors do
      s := s ++ s!" {← exportName c} {← exportExpr (← getConstInfoCtor c).type}"
    pure s

end

/-- Run an exporter action in `CoreM`, starting from the empty state. -/
def runExportM {α : Type} (m : ExportM α) : CoreM α := m.run' default

-- #eval runExportM (exportDef `Lean.Expr)
end Export

end Lean
