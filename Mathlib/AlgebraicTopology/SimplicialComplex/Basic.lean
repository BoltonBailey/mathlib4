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
every singleton. These are defined first defining `PreAbstractSimplicialComplex`,
which does not require the presence of singletons, and then defining `AbstractSimplicialComplex` as
an extension.

This is related to the geometrical notion of simplicial complexes, which are then defined under the
name `Geometry.SimplicialComplex` using affine combinations in another file.

## Main declarations

* `PreAbstractSimplicialComplex ι`: An abstract simplicial complex with vertices of type `ι`.
* `AbstractSimplicialComplex ι`: An abstract simplicial complex with vertices of type `ι` which
  contains all singletons.

## Notation

* `s ∈ K` means that `s` is a face of `K`.
* `K ≤ L` means that the faces of `K` are faces of `L`.

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

attribute [simp] PreAbstractSimplicialComplex.empty_notMem

namespace PreAbstractSimplicialComplex

instance : SetLike (PreAbstractSimplicialComplex ι) (Finset ι) where
  coe K := K.faces
  coe_injective' K _ _ := by
    cases K
    congr

/-- The complex consisting of only the faces present in both of its arguments. -/
instance : Min (PreAbstractSimplicialComplex ι) where
  min K L :=
    { faces := K.faces ∩ L.faces
      empty_notMem h := K.empty_notMem (Set.inter_subset_left h)
      down_closed hs hst ht := ⟨K.down_closed hs.1 hst ht, L.down_closed hs.2 hst ht⟩ }

/-- The complex consisting of all faces present in either of its arguments. -/
instance : Max (PreAbstractSimplicialComplex ι) where
  max K L :=
    { faces := K.faces ∪ L.faces
      empty_notMem := by
        simp only [Set.mem_union, not_or]
        exact ⟨K.empty_notMem, L.empty_notMem⟩
      down_closed := by
        rintro s t (hs | hs) hst ht
        · exact Or.inl (K.down_closed hs hst ht)
        · exact Or.inr (L.down_closed hs hst ht) }

instance : LE (PreAbstractSimplicialComplex ι) where
  le K L := K.faces ⊆ L.faces

instance : LT (PreAbstractSimplicialComplex ι) where
  lt K L := K.faces ⊂ L.faces

instance : PartialOrder (PreAbstractSimplicialComplex ι) :=
  PartialOrder.lift (fun K => K.faces) (fun _ _ => PreAbstractSimplicialComplex.ext)

instance : SupSet (PreAbstractSimplicialComplex ι) where
  sSup s :=
    { faces := ⋃ K ∈ s, K.faces
      empty_notMem := by
        simp [Set.mem_iUnion, empty_notMem]
      down_closed {s'} {t} hs hst ht := by
        simp only [Set.mem_iUnion] at hs ⊢
        obtain ⟨K, hK, hsK⟩ := hs
        exact ⟨K, hK, K.down_closed hsK hst ht⟩ }

instance : InfSet (PreAbstractSimplicialComplex ι) where
  sInf s :=
    { faces := (⋂ K ∈ s, K.faces) ∩ { t | t.Nonempty }
      empty_notMem := fun ⟨_, h⟩ => Finset.not_nonempty_empty h
      down_closed {s'} {t} := by
        intro ⟨hs, hs'⟩ hst ht
        constructor
        · simp only [Set.mem_iInter] at hs ⊢
          intro K hK
          exact K.down_closed (hs K hK) hst ht
        · exact ht }

instance : Top (PreAbstractSimplicialComplex ι) where
  top :=
    { faces := { s | s.Nonempty }
      empty_notMem := by simp
      down_closed _ _ ht := ht }

instance : Bot (PreAbstractSimplicialComplex ι) where
  bot :=
    { faces := { s | False }
      empty_notMem := by simp
      down_closed hs _ _ := hs.elim }

instance : CompleteSemilatticeSup (PreAbstractSimplicialComplex ι) where
  le_sSup _ _ hK := Set.subset_biUnion_of_mem hK
  sSup_le _ _ hK := Set.iUnion₂_subset hK

instance : CompleteSemilatticeInf (PreAbstractSimplicialComplex ι) where
  sInf_le _ _ hK := Set.inter_subset_left.trans (Set.biInter_subset_of_mem hK)
  le_sInf _ K hK _ ht :=
    ⟨Set.mem_iInter₂.mpr (fun L hL => hK L hL ht),
      Finset.nonempty_iff_ne_empty.mpr (fun h => K.empty_notMem (h ▸ ht))⟩

instance : CompleteLattice (PreAbstractSimplicialComplex ι) where
  inf := min
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ := Set.subset_inter
  sup := max
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ hK hL := Set.union_subset hK hL
  le_top K _ ht := Finset.nonempty_iff_ne_empty.mpr (fun h => K.empty_notMem (h ▸ ht))
  bot_le _ _ ht := ht.elim


end PreAbstractSimplicialComplex


/--
An `AbstractSimplicialComplex` is a `PreAbstractSimplicialComplex` which contains all singletons.
-/
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
def PreAbstractSimplicialComplex.toAbstractSimplicialComplex_union_singleton
    (K : PreAbstractSimplicialComplex ι) :
    AbstractSimplicialComplex ι :=
  { faces := K.faces ∪ { s | ∃ v, s = {v} }
    empty_notMem := by
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or]
      exact ⟨K.empty_notMem, fun ⟨_, h⟩ => Finset.singleton_ne_empty _ h.symm⟩
    down_closed {s} {t} hs hts ht := by
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

instance : SetLike (AbstractSimplicialComplex ι) (Finset ι) where
  coe K := K.faces
  coe_injective' _ _ _ := by
    ext
    grind

/-- The complex consisting of only the faces present in both of its arguments. -/
instance : Min (AbstractSimplicialComplex ι) where
  min K L :=
    { K.toPreAbstractSimplicialComplex ⊓ L.toPreAbstractSimplicialComplex with
      singleton_mem v := ⟨K.singleton_mem v, L.singleton_mem v⟩ }

/-- The complex consisting of all faces present in either of its arguments. -/
instance : Max (AbstractSimplicialComplex ι) where
  max K L :=
    { K.toPreAbstractSimplicialComplex ⊔ L.toPreAbstractSimplicialComplex with
      singleton_mem v := Or.inl (K.singleton_mem v) }

instance : LE (AbstractSimplicialComplex ι) where
  le K L := K.faces ⊆ L.faces

instance : LT (AbstractSimplicialComplex ι) where
  lt K L := K.faces ⊂ L.faces

instance : PartialOrder (AbstractSimplicialComplex ι) :=
  PartialOrder.lift (fun K => K.faces) (fun _ _ => AbstractSimplicialComplex.ext)

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

instance : SupSet (AbstractSimplicialComplex ι) where
  sSup s :=
    { faces := (⋃ K ∈ s, K.faces) ∪ { t | ∃ v, t = {v} }
      empty_notMem := by
        simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists]
        exact ⟨fun K hK => K.empty_notMem, fun _ h => Finset.singleton_ne_empty _ h.symm⟩
      down_closed {t₁} {t₂} ht ht₁t₂ ht₂ := by
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

instance : InfSet (AbstractSimplicialComplex ι) where
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

instance : Top (AbstractSimplicialComplex ι) where
  top :=
    { (⊤ : PreAbstractSimplicialComplex ι) with
      singleton_mem _ := Finset.singleton_nonempty _ }

lemma top_toPreAbstractSimplicialComplex :
    (⊤ : AbstractSimplicialComplex ι).toPreAbstractSimplicialComplex = ⊤ :=
  rfl

instance : Bot (AbstractSimplicialComplex ι) where
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

instance : CompleteSemilatticeSup (AbstractSimplicialComplex ι) where
  le_sSup _ K hK _ ht := Or.inl (Set.mem_biUnion hK ht)
  sSup_le _ L hL _ ht := by
    cases ht with
    | inl ht =>
      simp only [Set.mem_iUnion] at ht
      obtain ⟨K, hK, htK⟩ := ht
      exact hL K hK htK
    | inr ht =>
      obtain ⟨v, hv⟩ := ht
      exact hv ▸ L.singleton_mem v

instance : CompleteSemilatticeInf (AbstractSimplicialComplex ι) where
  sInf_le _ _ hK := Set.inter_subset_left.trans (Set.biInter_subset_of_mem hK)
  le_sInf _ K hK _ ht :=
    ⟨Set.mem_iInter₂.mpr (fun L hL => hK L hL ht),
      Finset.nonempty_iff_ne_empty.mpr (fun h => K.empty_notMem (h ▸ ht))⟩

instance : CompleteLattice (AbstractSimplicialComplex ι) where
  inf := min
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ := Set.subset_inter
  sup := max
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ := Set.union_subset
  le_top K _ ht := Finset.nonempty_iff_ne_empty.mpr (fun h => K.empty_notMem (h ▸ ht))
  bot_le K _ ht := by
    obtain ⟨v, hv⟩ := ht
    exact hv ▸ K.singleton_mem v

end AbstractSimplicialComplex

end
