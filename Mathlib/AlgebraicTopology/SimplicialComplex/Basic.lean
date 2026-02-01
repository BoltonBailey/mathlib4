/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Independent

/-!
# Abstract Simplicial complexes

In this file, we define abstract simplicial complexes.
An abstract simplicial complex is a downwards-closed collection of nonempty finite sets containing
every Singleton. These are defined first defining `PreAbstractSimplicialComplex`,
which does not require the presence of singletons, and then defining `AbstractSimplicialComplex` as
an extension.

This is related to the geometrical notion of simplicial complexes, which are then defined under the
name `Geometry.SimplicialComplex` using affine combinations in another file.

## Main declarations

* `PreAbstractSimplicialComplex ι`: An abstract simplicial complex with vertices of type `ι`.
* `AbstractSimplicialComplex ι`: An abstract simplicial complex with vertices of type `ι` which
  contains all singletons.

## Notation

`s ∈ K` means that `s` is a face of `K`.

`K ≤ L` means that the faces of `K` are faces of `L`.

-/

@[expose] public section


open Finset Set

variable (ι : Type*)

/-- An abstract simplicial complex is a collection of nonempty finite sets of points ("faces")
which is downwards closed, i.e., any nonempty subset of a face is also a face.
-/
@[ext]
structure PreAbstractSimplicialComplex where
  /-- the faces of this simplicial complex: currently, given by their spanning vertices -/
  faces : Set (Finset ι)
  /-- the empty set is not a face: hence, all faces are non-empty -/
  empty_notMem : ∅ ∉ faces
  /-- faces are downward closed: a non-empty subset of its spanning vertices spans another face -/
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces

namespace PreAbstractSimplicialComplex

/-- The complex consisting of only the faces present in both of its arguments. -/
instance : Min (PreAbstractSimplicialComplex ι) :=
  ⟨fun K L =>
    { faces := K.faces ∩ L.faces
      empty_notMem := fun h => K.empty_notMem (Set.inter_subset_left h)
      down_closed := fun hs hst ht => ⟨K.down_closed hs.1 hst ht, L.down_closed hs.2 hst ht⟩ }⟩

/-- The complex consisting of all faces present in either of its arguments. -/
instance : Max (PreAbstractSimplicialComplex ι) :=
  ⟨fun K L =>
    { faces := K.faces ∪ L.faces
      empty_notMem := by
        simp only [Set.mem_union, not_or]
        exact ⟨K.empty_notMem, L.empty_notMem⟩
      down_closed := by
        rintro s t (hs | hs) hst ht
        · grind only [instMax._simp_1, down_closed]
        · grind only [instMax._simp_1, down_closed]
      }⟩

instance : LE (PreAbstractSimplicialComplex ι) :=
  ⟨fun K L => K.faces ⊆ L.faces⟩

instance : LT (PreAbstractSimplicialComplex ι) :=
  ⟨fun K L => K.faces ⊂ L.faces⟩

instance : CompleteLattice (PreAbstractSimplicialComplex ι) := {
  PartialOrder.lift (fun K => K.faces) (fun _ _ => PreAbstractSimplicialComplex.ext) with
  inf := min
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ h1 h2 := Set.subset_inter h1 h2
  sup := max
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ hK hL := Set.union_subset hK hL
  sSup s :=
    { faces := ⋃ K ∈ s, K.faces
      empty_notMem := by
        simp only [Set.mem_iUnion, not_exists]
        exact fun K hK => K.empty_notMem
      down_closed := by
        intro s' t hs hst ht
        simp only [Set.mem_iUnion] at hs ⊢
        obtain ⟨K, hK, hsK⟩ := hs
        exact ⟨K, hK, K.down_closed hsK hst ht⟩ }
  le_sSup _ _ hK := Set.subset_biUnion_of_mem hK
  sSup_le _ _ hK := Set.iUnion₂_subset hK
  sInf s :=
    { faces := (⋂ K ∈ s, K.faces) ∩ { t | t.Nonempty }
      empty_notMem := by
        simp only [Set.mem_inter_iff, Set.mem_setOf]
        exact fun ⟨_, h⟩ => Finset.not_nonempty_empty h
      down_closed := by
        intro s' t ⟨hs, hs'⟩ hst ht
        constructor
        · simp only [Set.mem_iInter] at hs ⊢
          intro K hK
          exact K.down_closed (hs K hK) hst ht
        · exact ht }
  sInf_le _ _ hK := Set.inter_subset_left.trans (Set.biInter_subset_of_mem hK)
  le_sInf _ K hK t ht :=
    ⟨Set.mem_iInter₂.mpr (fun L hL => hK L hL ht),
      Finset.nonempty_iff_ne_empty.mpr (fun h => K.empty_notMem (h ▸ ht))⟩
  top :=
    { faces := { s | s.Nonempty }
      empty_notMem := by simp
      down_closed _ _ ht := ht }
  le_top K _ ht := Finset.nonempty_iff_ne_empty.mpr (fun h => K.empty_notMem (h ▸ ht))
  bot :=
    { faces := { s | False }
      empty_notMem := by simp
      down_closed hs _ _ := hs.elim }
  bot_le _ _ ht := ht.elim }


end PreAbstractSimplicialComplex

@[ext]
structure AbstractSimplicialComplex extends PreAbstractSimplicialComplex ι where
  /-- every singleton is a face -/
  singleton_mem : ∀ v : ι, {v} ∈ faces

/-- Convert a `PreAbstractSimplicialComplex` satisfying `IsAbstract` to an
`AbstractSimplicialComplex`. -/
def PreAbstractSimplicialComplex.toAbstractSimplicialComplex
    (K : PreAbstractSimplicialComplex ι) (h : ∀ v : ι, {v} ∈ K.faces) :
    AbstractSimplicialComplex ι :=
  { K with singleton_mem := h }

/-- The closure of a `PreAbstractSimplicialComplex` to an `AbstractSimplicialComplex` by adding
all singletons. -/
def PreAbstractSimplicialComplex.abstractClosure (K : PreAbstractSimplicialComplex ι) :
    AbstractSimplicialComplex ι :=
  { faces := K.faces ∪ { s | ∃ v, s = {v} }
    empty_notMem := by
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or]
      exact ⟨K.empty_notMem, fun ⟨_, h⟩ => Finset.singleton_ne_empty _ h.symm⟩
    down_closed := by
      intro s t hs hts ht
      cases hs with
      | inl hs => exact Or.inl (K.down_closed hs hts ht)
      | inr hs =>
        obtain ⟨v, hv⟩ := hs
        rw [hv, Finset.subset_singleton_iff] at hts
        cases hts with
        | inl h => exact (ht.ne_empty h).elim
        | inr h => exact Or.inr ⟨v, h⟩
    singleton_mem v := Or.inr ⟨v, rfl⟩ }

namespace AbstractSimplicialComplex

variable {ι}

/-- The complex consisting of only the faces present in both of its arguments. -/
instance : Min (AbstractSimplicialComplex ι) :=
  ⟨fun K L =>
    { K.toPreAbstractSimplicialComplex ⊓ L.toPreAbstractSimplicialComplex with
      singleton_mem v := ⟨K.singleton_mem v, L.singleton_mem v⟩ }⟩

/-- The complex consisting of all faces present in either of its arguments. -/
instance : Max (AbstractSimplicialComplex ι) :=
  ⟨fun K L =>
    { K.toPreAbstractSimplicialComplex ⊔ L.toPreAbstractSimplicialComplex with
      singleton_mem v := Or.inl (K.singleton_mem v) }⟩

instance : LE (AbstractSimplicialComplex ι) :=
  ⟨fun K L => K.faces ⊆ L.faces⟩

instance : LT (AbstractSimplicialComplex ι) :=
  ⟨fun K L => K.faces ⊂ L.faces⟩

theorem toPreAbstractSimplicialComplex_injective :
    Function.Injective (toPreAbstractSimplicialComplex (ι := ι)) :=
  fun _ _ h => AbstractSimplicialComplex.ext (congrArg PreAbstractSimplicialComplex.faces h)

@[simp]
theorem toPreAbstractSimplicialComplex_le_iff {K L : AbstractSimplicialComplex ι} :
    K.toPreAbstractSimplicialComplex ≤ L.toPreAbstractSimplicialComplex ↔ K ≤ L :=
  Iff.rfl

@[simp]
theorem toPreAbstractSimplicialComplex_lt_iff {K L : AbstractSimplicialComplex ι} :
    K.toPreAbstractSimplicialComplex < L.toPreAbstractSimplicialComplex ↔ K < L :=
  Iff.rfl

-- TODO: Ideally the instance for `CompleteLattice (AbstractSimplicialComplex ι)`
-- would be done more parsimoniously by lifting from `PreAbstractSimplicialComplex`,
-- This would require a constructor that allows us to construct a `CompleteLattice` instance
-- from a `CompleteLattice` instance via an injection, and a proof that the operations
-- respect the injection.
instance : CompleteLattice (AbstractSimplicialComplex ι) := {
  PartialOrder.lift (fun K => K.faces) (fun _ _ => AbstractSimplicialComplex.ext) with
  inf := min
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ h1 h2 := Set.subset_inter h1 h2
  sup := max
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ hK hL := Set.union_subset hK hL
  sSup s :=
    { faces := (⋃ K ∈ s, K.faces) ∪ { t | ∃ v, t = {v} }
      empty_notMem := by
        simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists]
        exact ⟨fun K hK => K.empty_notMem, fun _ h => Finset.singleton_ne_empty _ h.symm⟩
      down_closed := by
        intro t₁ t₂ ht ht₁t₂ ht₂
        cases ht with
        | inl ht =>
          simp only [Set.mem_iUnion] at ht
          obtain ⟨K, hK, htK⟩ := ht
          exact Or.inl (Set.mem_iUnion₂.mpr ⟨K, hK, K.down_closed htK ht₁t₂ ht₂⟩)
        | inr ht =>
          obtain ⟨v, hv⟩ := ht
          rw [hv, Finset.subset_singleton_iff] at ht₁t₂
          cases ht₁t₂ with
          | inl h => exact (ht₂.ne_empty h).elim
          | inr h => exact Or.inr ⟨v, h⟩
      singleton_mem v := Or.inr ⟨v, rfl⟩ }
  le_sSup _ K hK := by intro t ht; exact Or.inl (Set.mem_biUnion hK ht)
  sSup_le _ L hL := fun _ ht => by
    cases ht with
    | inl ht =>
      simp only [Set.mem_iUnion] at ht
      obtain ⟨K, hK, htK⟩ := ht
      exact hL K hK htK
    | inr ht =>
      obtain ⟨v, hv⟩ := ht
      exact hv ▸ L.singleton_mem v
  sInf s :=
    { faces := (⋂ K ∈ s, K.faces) ∩ { t | t.Nonempty }
      empty_notMem := by
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.not_nonempty_empty, and_false,
          not_false_eq_true]
      down_closed := by
        intro t₁ t₂ ⟨ht₁, ht₁'⟩ ht₁t₂ ht₂
        constructor
        · simp only [Set.mem_iInter] at ht₁ ⊢
          intro K hK
          exact K.down_closed (ht₁ K hK) ht₁t₂ ht₂
        · exact ht₂
      singleton_mem v := by
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq,
          Finset.singleton_nonempty, and_true]
        intro K hK
        exact K.singleton_mem v }
  sInf_le := fun _ K hK => Set.inter_subset_left.trans (Set.biInter_subset_of_mem hK)
  le_sInf _ K hK t ht :=
    ⟨Set.mem_iInter₂.mpr (fun L hL => hK L hL ht),
      Finset.nonempty_iff_ne_empty.mpr (fun h => K.empty_notMem (h ▸ ht))⟩
  top :=
    { (⊤ : PreAbstractSimplicialComplex ι) with
      singleton_mem _ := Finset.singleton_nonempty _ }
  le_top K _ ht := Finset.nonempty_iff_ne_empty.mpr (fun h => K.empty_notMem (h ▸ ht))
  bot :=
    { faces := { s | ∃ v, s = {v} }
      empty_notMem := by simp
      down_closed := by
        intro s t ⟨v, hv⟩ hts ht
        rw [hv, Finset.subset_singleton_iff] at hts
        cases hts with
        | inl h => exact (ht.ne_empty h).elim
        | inr h => exact ⟨v, h⟩
      singleton_mem v := ⟨v, rfl⟩ }
  bot_le K _ ht := by obtain ⟨v, hv⟩ := ht; exact hv ▸ K.singleton_mem v }



end AbstractSimplicialComplex

end
