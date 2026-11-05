/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SignedGroupRingFace
import Verification.AnticliqueSubcolumns
import Mathlib.Data.ZMod.Basic

/-!
# Original Witt Quotient

The manuscript's literal integral Witt stratum quotients, in the
original mutable and frozen coordinates. No signature lattice is used.
-/
noncomputable section
namespace Verification.OriginalWittQuotient
open MonoidAlgebra Verification.SignedGroupRingFace
variable {V C : Type*}

abbrev Bits (V C : Type*) := (V ⊕ C) → ZMod 2
abbrev Group (V C : Type*) := Multiplicative (Bits V C)
abbrev Ambient (V C : Type*) := MonoidAlgebra ℤ (Group V C)

def normalVector (i : V) : Group V C := by
  classical
  exact Multiplicative.ofAdd (Pi.single (Sum.inl i) 1)

def columnVector (B : (V ⊕ C) → V → ℤ) (i : V) : Group V C :=
  Multiplicative.ofAdd (fun a => (B a i : ZMod 2))

def generator (B : (V ⊕ C) → V → ℤ) (I : Finset V) : (I ⊕ I) → Group V C :=
  Sum.elim (fun i => normalVector i.val) (fun i => columnVector B i.val)

def generatorSign (I : Finset V) : (I ⊕ I) → ℤ := Sum.elim (fun _ => 1) (fun _ => -1)

def relationIdeal (B : (V ⊕ C) → V → ℤ) (I : Finset V) : Ideal (Ambient V C) :=
  relations (generator B I) (generatorSign I)

abbrev Stratum (B : (V ⊕ C) → V → ℤ) (I : Finset V) := Ambient V C ⧸ relationIdeal B I

theorem normal_relation (B : (V ⊕ C) → V → ℤ) (I : Finset V) (i : I) :
    of ℤ (Group V C) (normalVector i.val) - 1 ∈ relationIdeal B I := by
  simpa [relationIdeal,relation,generator,generatorSign] using
    (Ideal.subset_span (Set.mem_range_self (Sum.inl i)) :
      relation (generator B I (Sum.inl i)) (generatorSign I (Sum.inl i)) ∈
        relations (generator B I) (generatorSign I))

theorem column_relation (B : (V ⊕ C) → V → ℤ) (I : Finset V) (i : I) :
    of ℤ (Group V C) (columnVector B i.val) + 1 ∈ relationIdeal B I := by
  simpa [relationIdeal,relation,generator,generatorSign] using
    (Ideal.subset_span (Set.mem_range_self (Sum.inr i)) :
      relation (generator B I (Sum.inr i)) (generatorSign I (Sum.inr i)) ∈
        relations (generator B I) (generatorSign I))

theorem ideal_monotone (B : (V ⊕ C) → V → ℤ) {I J : Finset V} (h : I ⊆ J) :
    relationIdeal B I ≤ relationIdeal B J := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  cases i with
  | inl i => exact Ideal.subset_span (Set.mem_range_self (Sum.inl (⟨i.val,h i.property⟩ : J)))
  | inr i => exact Ideal.subset_span (Set.mem_range_self (Sum.inr (⟨i.val,h i.property⟩ : J)))

def coordinate (j : V) : Group V C →* Multiplicative (ZMod 2) where
  toFun a := Multiplicative.ofAdd (Multiplicative.toAdd a (Sum.inl j))
  map_one' := rfl
  map_mul' _ _ := rfl

theorem old_normal_zero {I : Finset V} (j : V) (hj : j ∉ I) (i : I) :
    coordinate (C := C) j (normalVector i.val) = 1 := by
  classical
  have h : (Sum.inl j : V ⊕ C) ≠ Sum.inl i.val := by
    intro e
    exact hj (Sum.inl.inj e ▸ i.property)
  simp [coordinate,normalVector,Pi.single_apply,h]

theorem old_column_zero (B : (V ⊕ C) → V → ℤ) (I : Finset V) (j : V)
    (hB : ∀ i : I, B (Sum.inl j) i.val = 0) (i : I) :
    coordinate j (columnVector B i.val) = 1 := by
  simp [coordinate,columnVector,hB i]

theorem old_generators_zero (B : (V ⊕ C) → V → ℤ) (I : Finset V) (j : V)
    (hj : j ∉ I) (hB : ∀ i : I, B (Sum.inl j) i.val = 0) :
    ∀ i, coordinate j (generator B I i) = 1 := by
  intro i
  cases i with
  | inl i => exact old_normal_zero j hj i
  | inr i => exact old_column_zero B I j hB i

def residue (B : (V ⊕ C) → V → ℤ) (I J : Finset V) (j : V)
    (h : I ⊆ J) (hj : j ∉ I) (hB : ∀ i : I, B (Sum.inl j) i.val = 0) :
    Stratum B I →ₗ[ℤ] Stratum B J :=
  face (coordinate j) (generator B I) (generatorSign I)
    (old_generators_zero B I j hj hB) (relationIdeal B J) (ideal_monotone B h)

theorem residue_mk (B : (V ⊕ C) → V → ℤ) (I J : Finset V) (j : V)
    (h : I ⊆ J) (hj : j ∉ I) (hB : ∀ i : I, B (Sum.inl j) i.val = 0)
    (a : Ambient V C) :
    residue B I J j h hj hB (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (projection (coordinate j) a) := rfl

theorem residue_monomial (B : (V ⊕ C) → V → ℤ) (I J : Finset V) (j : V)
    (h : I ⊆ J) (hj : j ∉ I) (hB : ∀ i : I, B (Sum.inl j) i.val = 0)
    (a : Group V C) :
    residue B I J j h hj hB (Ideal.Quotient.mk _ (of ℤ _ a)) =
      weight (coordinate j) a • Ideal.Quotient.mk _ (of ℤ _ a) :=
  face_monomial (coordinate j) (generator B I) (generatorSign I)
    (old_generators_zero B I j hj hB) (relationIdeal B J) (ideal_monotone B h) a

theorem weight_coordinate (a : Group V C) (j : V) :
    weight (coordinate j) a = (Multiplicative.toAdd a (Sum.inl j)).val := by
  classical
  let b := Multiplicative.toAdd a (Sum.inl j)
  have hb : b.val < 2 := ZMod.val_lt b
  by_cases h : b = 0
  · simp [weight,coordinate,← show b = Multiplicative.toAdd a (Sum.inl j) from rfl,h]
  · have hv : b.val ≠ 0 := by intro h0; exact h ((ZMod.val_eq_zero _).mp h0)
    have he : b.val = 1 := by omega
    simp only [weight, if_neg (show coordinate j a ≠ 1 from h)]
    change 1 = (b.val : ℤ)
    simp [he]

theorem residues_commute (B : (V ⊕ C) → V → ℤ)
    (I J J' K : Finset V) (i j : V)
    (hIJ : I ⊆ J) (hIJs : I ⊆ J') (hJK : J ⊆ K) (hJsK : J' ⊆ K)
    (hi : i ∉ I) (hj : j ∉ I) (hjJ : j ∉ J) (hiJs : i ∉ J')
    (hBi : ∀ a : I, B (Sum.inl i) a.val = 0)
    (hBj : ∀ a : I, B (Sum.inl j) a.val = 0)
    (hBjJ : ∀ a : J, B (Sum.inl j) a.val = 0)
    (hBiJs : ∀ a : J', B (Sum.inl i) a.val = 0) (x : Stratum B I) :
    residue B J K j hJK hjJ hBjJ (residue B I J i hIJ hi hBi x) =
      residue B J' K i hJsK hiJs hBiJs (residue B I J' j hIJs hj hBj x) := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [residue_mk,projections_commute (coordinate i) (coordinate j)]

#print axioms residues_commute
#print axioms Bits
#print axioms Group
#print axioms Ambient
#print axioms normalVector
#print axioms columnVector
#print axioms generator
#print axioms generatorSign
#print axioms relationIdeal
#print axioms Stratum
#print axioms normal_relation
#print axioms column_relation
#print axioms ideal_monotone
#print axioms coordinate
#print axioms old_normal_zero
#print axioms old_column_zero
#print axioms old_generators_zero
#print axioms residue
#print axioms residue_mk
#print axioms residue_monomial
#print axioms weight_coordinate
end Verification.OriginalWittQuotient
