/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ResidualScalarReentry

/-!
# Residual Reindex AS

Reindexing the actual residual AS columns into finite mutable/frozen
coordinates preserves their split injections. The row reconstruction is
explicit; no AS assumption on the new matrix is introduced.
-/
noncomputable section
namespace Verification.ResidualReindexAS
open Verification.ResidualScalarReentry Verification.FreezingIndex
open Verification.ActualFreezingRows Verification.ActualResidualColumns
open Verification.ActualScalarFreezing Verification.AnticliqueSubcolumns
open Verification.FreezingLattice Verification.FrozenAcyclicCover
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
attribute [local instance] Verification.ActualFreezingConstraint.remainingFintype
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)
variable {m r : ℕ} (h : Remaining κ n B v ≃ Fin m)
variable (e : QuotientLattice κ n B v ≃ₗ[ℤ] (Fin r →₀ ℤ)) (I : Finset (Fin m))

def selectedOriginal : Finset (Fin n) := I.image (fun i => (h.symm i).val)

def selectedEquiv : I ≃ selectedOriginal κ n B v h I :=
  Equiv.ofBijective (fun i => ⟨(h.symm i.val).val, Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩)
    (by
      constructor
      · intro i j hij
        apply Subtype.ext
        have hv : (h.symm i.val).val = (h.symm j.val).val :=
          congrArg (fun z : selectedOriginal κ n B v h I => z.val) hij
        exact h.symm.injective (Subtype.ext hv)
      · intro j
        obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp j.property
        exact ⟨⟨i,hi⟩,Subtype.ext hij⟩)

def coefficientEquiv : (I →₀ ℤ) ≃ₗ[ℤ] (selectedOriginal κ n B v h I →₀ ℤ) :=
  Finsupp.domLCongr (selectedEquiv κ n B v h I)

omit [Fintype κ] in
theorem outside_not_selected (s : Outside κ n B v (selectedOriginal κ n B v h I)) : h s.val ∉ I := by
  intro hs
  apply s.property
  exact Finset.mem_image.mpr ⟨h s.val,hs,by simp⟩

def rowMap : (Rows (C := Fin r) I →₀ ℤ) →ₗ[ℤ]
    ResidualRows κ n B v (selectedOriginal κ n B v h I) where
  toFun x :=
    (Finsupp.equivFunOnFinite.symm (fun s : Outside κ n B v (selectedOriginal κ n B v h I) =>
      x ⟨Sum.inl (h s.val),by
        intro i hi heq
        exact outside_not_selected κ n B v h I s (Sum.inl.inj heq ▸ hi)⟩),
      e.symm (Finsupp.equivFunOnFinite.symm (fun k : Fin r => x ⟨Sum.inr k,by simp⟩)))
  map_add' x y := by
    apply Prod.ext
    · ext s; rfl
    · change e.symm _ = e.symm _ + e.symm _
      rw [← map_add]
      apply congrArg e.symm
      ext k
      rfl
  map_smul' a x := by
    apply Prod.ext
    · ext s; rfl
    · change e.symm _ = a • e.symm _
      rw [← map_smul]
      apply congrArg e.symm
      ext k
      rfl

theorem rowMap_column (i : I) :
    rowMap κ n B v h e I
      (column (fun q j => reindexedMatrix κ n B v h e q (Sum.inl j)) I i) =
      residualColumn κ n B v (selectedOriginal κ n B v h I) (selectedEquiv κ n B v h I i) := by
  apply Prod.ext
  · ext s
    change B (Sum.inl (h.symm (h s.val)).val) (Sum.inl (h.symm i.val).val) =
      B (Sum.inl s.val.val) (Sum.inl (h.symm i.val).val)
    rw [Equiv.symm_apply_apply]
  · change e.symm (Finsupp.equivFunOnFinite.symm
      (fun k => e (frozenColumn κ n B v (h.symm i.val)) k)) =
        frozenColumn κ n B v (h.symm i.val)
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    ext k
    rfl

theorem maps_compatible :
    (rowMap κ n B v h e I).comp
      (selectedMap (fun q j => reindexedMatrix κ n B v h e q (Sum.inl j)) I) =
      (residualMatrix κ n B v (selectedOriginal κ n B v h I)).comp
        (coefficientEquiv κ n B v h I).toLinearMap := by
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, selectedMap,
    Finsupp.linearCombination_single, one_smul]
  rw [rowMap_column]
  change _ = residualMatrix κ n B v (selectedOriginal κ n B v h I)
    (Finsupp.domLCongr (selectedEquiv κ n B v h I) (Finsupp.single i 1))
  simp only [Finsupp.domLCongr_single, residualMatrix, Finsupp.linearCombination_single, one_smul]

theorem AS_transport
    (hAS : Function.Injective (residualMatrix κ n B v (selectedOriginal κ n B v h I)) ∧
      Saturated (LinearMap.range (residualMatrix κ n B v (selectedOriginal κ n B v h I)))) :
    AS (fun q j => reindexedMatrix κ n B v h e q (Sum.inl j)) I := by
  obtain ⟨s,hs⟩ := PrimitiveLattice.primitive_columns_split_compatible _ hAS.1 hAS.2
  let t := (coefficientEquiv κ n B v h I).symm.toLinearMap.comp
    ((LinearMap.fst ℤ _ _).comp (s.toLinearMap.comp (rowMap κ n B v h e I)))
  have ht : Function.LeftInverse t
      (selectedMap (fun q j => reindexedMatrix κ n B v h e q (Sum.inl j)) I) := by
    intro x
    change (coefficientEquiv κ n B v h I).symm
      (s (rowMap κ n B v h e I (selectedMap _ I x))).1 = x
    have hx := LinearMap.congr_fun (maps_compatible κ n B v h e I) x
    change rowMap κ n B v h e I (selectedMap _ I x) =
      residualMatrix κ n B v (selectedOriginal κ n B v h I) (coefficientEquiv κ n B v h I x) at hx
    rw [hx, hs]
    exact (coefficientEquiv κ n B v h I).symm_apply_apply x
  exact ⟨ht.injective,CliqueSaturation.split_range_saturated _ _ ht⟩

#print axioms selectedOriginal
#print axioms selectedEquiv
#print axioms coefficientEquiv
#print axioms outside_not_selected
#print axioms rowMap
#print axioms rowMap_column
#print axioms maps_compatible
#print axioms AS_transport
end Verification.ResidualReindexAS
