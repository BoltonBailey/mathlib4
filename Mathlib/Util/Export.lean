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

/-- The kinds of item in an export file. -/
inductive Entry
  | name (n : Name)
  | level (n : Level)
  | expr (n : Expr)
  | defn (n : Name)
deriving Inhabited

instance : Coe Name Entry := ⟨Entry.name⟩
instance : Coe Level Entry := ⟨Entry.level⟩
instance : Coe Expr Entry := ⟨Entry.expr⟩

/-- An allocator of indices for values of type `α`: the index already assigned to each value, and
the next free index. -/
structure Alloc (α) [BEq α] [Hashable α] where
  /-- The index assigned to each value exported so far. -/
  map : Std.HashMap α Nat
  /-- The next unused index. -/
  next : Nat
deriving Inhabited

/-- The exporter's state: index allocators for names, universe levels and expressions, the set of
declarations already written out, and a work stack. -/
structure State where
  /-- Index allocator for names; the anonymous name is preassigned index `0`. -/
  names : Alloc Name := ⟨(∅ : Std.HashMap Name Nat).insert Name.anonymous 0, 1⟩
  /-- Index allocator for universe levels; `Level.zero` is preassigned index `0`. -/
  levels : Alloc Level := ⟨(∅ : Std.HashMap Level Nat).insert .zero 0, 1⟩
  /-- Index allocator for expressions. -/
  exprs : Alloc Expr
  /-- The declarations that have already been written out. -/
  defs : Std.HashSet Name
  /-- A stack of flagged items. Unused by the current implementation. -/
  stk : Array (Bool × Entry)
deriving Inhabited

/-- Access to the allocator for `α` inside the exporter state. -/
class OfState (α : Type) [BEq α] [Hashable α] where
  /-- The allocator for `α` in the state. -/
  get : State → Alloc α
  /-- Update the allocator for `α` in the state. -/
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

/-- The monad the exporter runs in: `CoreM` with an `Export.State`. -/
abbrev ExportM := StateT Export.State CoreM

namespace Export

/-- Allocate a fresh index for `a` in the allocator for `α`, record it, and return it. -/
def alloc {α} [BEq α] [Hashable α] [OfState α] (a : α) : ExportM Nat := do
  let n := (OfState.get (α := α) (← get)).next
  modify <| OfState.modify (α := α) fun s ↦ {map := s.map.insert a n, next := n + 1}
  pure n

/-- Export the name `n` and return its index, reusing the index if it has been exported before. The
anonymous name has index `0`; any other name is written as a `#NS` or `#NI` line referring to
the index of its prefix. -/
def exportName (n : Name) : ExportM Nat := do
  match (← get).names.map[n]? with
  | some i => pure i
  | none => match n with
    | .anonymous => pure 0
    | .num p a => let i ← alloc n; IO.println s!"{i} #NI {← exportName p} {a}"; pure i
    | .str p s => let i ← alloc n; IO.println s!"{i} #NS {← exportName p} {s}"; pure i

/-- Export the universe level `L` and return its index, reusing the index if it has been exported
before. `Level.zero` has index `0`; any other level is written as a `#US`, `#UM`, `#UIM` or
`#UP` line referring to the indices of its components. -/
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

/-- The export-format tag for a binder annotation: `#BD`, `#BI`, `#BS` or `#BC`. -/
def biStr : BinderInfo → String
  | BinderInfo.default        => "#BD"
  | BinderInfo.implicit       => "#BI"
  | BinderInfo.strictImplicit => "#BS"
  | BinderInfo.instImplicit   => "#BC"

open ConstantInfo in
mutual

/-- Export the expression `E` and return its index, reusing the index if it has been exported
before. Each node is written as one line, tagged `#EV`, `#ES`, `#EC`, `#EA`, `#EL`, `#EP`,
`#EN`, `#ET` or `#EJ` according to its constructor and referring to the indices of its subterms;
constants are exported first with `exportDef`. Free variables, metavariables and `mdata` are not
supported. -/
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

/-- Export the declaration `n` together with everything it depends on, unless it has been exported
already.

The constants used in its value are exported first. Then a single line is written according to
the kind of declaration: `#AX name type` for an axiom, `#DEF name type value` for a definition,
`#THM name type value` for a theorem, `#CN name type value` for an opaque constant, and `#QUOT`
for the quotient primitives; each of these is followed by the universe parameters. Names, types
and values are given by their indices.

An inductive type is written as `#IND numParams` (or `#MUT numParams k` for a family of `k`
types) followed, for each type, by its name, type and constructors with their types, and finally
the universe parameters. Its recursors are marked as exported at the same time. -/
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

/-- Run an exporter computation in `CoreM`, starting from the initial state. -/
def runExportM {α : Type} (m : ExportM α) : CoreM α := m.run' default

-- #eval runExportM (exportDef `Lean.Expr)
end Export

end Lean
