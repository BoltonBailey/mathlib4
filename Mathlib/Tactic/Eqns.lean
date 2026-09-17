/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Init
public meta import Lean.Meta.Eqns
public meta import Batteries.Lean.NameMapAttribute
public meta import Lean.Elab.Exception
public meta import Lean.Elab.InfoTree.Main

/-! # The `@[eqns]` attribute

This file provides the `eqns` attribute as a way of overriding the default equation lemmas. For
example

```lean4
def transpose {m n} (A : m → n → ℕ) : n → m → ℕ
  | i, j => A j i

theorem transpose_apply {m n} (A : m → n → ℕ) (i j) :
    transpose A i j = A j i := rfl

attribute [eqns transpose_apply] transpose

theorem transpose_const {m n} (c : ℕ) :
    transpose (fun (i : m) (j : n) => c) = fun j i => c := by
  funext i j -- the rw below does not work without this line
  rw [transpose]
```
-/

public meta section
open Lean Elab

/-- `@[eqns h₁ h₂ …]` replaces the equation lemmas of a definition `f` by the theorems `h₁ h₂ …`, so
that `rw [f]` and `simp [f]` unfold `f` through them instead of through the automatically
generated equations.

For example, after
```lean
def transpose {m n} (A : m → n → ℕ) : n → m → ℕ
  | i, j => A j i

theorem transpose_apply {m n} (A : m → n → ℕ) (i j) : transpose A i j = A j i := rfl

attribute [eqns transpose_apply] transpose
```
`rw [transpose]` rewrites with `transpose_apply` rather than with the pattern-matching equation. -/
syntax (name := eqns) "eqns" (ppSpace ident)* : attr

/-- The extension recording, for each definition tagged `@[eqns]`, the theorems that replace its
equation lemmas. -/
initialize eqnsAttribute : NameMapExtension (Array Name) ←
  registerNameMapAttribute {
    name  := `eqns
    descr := "Overrides the equation lemmas for a declaration to the provided list"
    add   := fun
    | declName, `(attr| eqns $[$names]*) => do
      -- We used to be able to check here if equational lemmas have already been registered in
      -- Leans `eqsnExt`, but that has been removed in https://github.com/leanprover-community/mathlib4/issues/8519, so no warning in that case.
      -- Now we just hope that the `GetEqnsFn` registered below will always run before
      -- Lean’s.
      names.mapM realizeGlobalConstNoOverloadWithInfo
    | _, _ => Lean.Elab.throwUnsupportedSyntax }

initialize Lean.Meta.registerGetEqnsFn (fun name => do
  pure (eqnsAttribute.find? (← getEnv) name))
