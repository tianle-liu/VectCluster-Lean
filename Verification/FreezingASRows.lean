/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AnticliqueSubcolumns

/-!
# Freezing AS Rows

Deleting mutable columns while relabeling their original rows as frozen
preserves AS. An explicit row map restores the original selected matrix;
the resulting splitting is constructed from the old primitive columns.
-/
noncomputable section
namespace Verification.FreezingASRows
open Verification.AnticliqueSubcolumns Verification.FreezingLattice
variable {V W C D : Type} [Fintype V] [Fintype W] [Fintype C] [Fintype D]
variable (g : W → V) (hg : Function.Injective g) (e : (W ⊕ D) ≃ (V ⊕ C))
variable (he : ∀ w, e (Sum.inl w) = Sum.inl (g w))
variable (B : (V ⊕ C) → V → ℤ) (I : Finset W)

def selectedOriginal : Finset V := by
  classical
  exact I.image g

def selectedEquiv : I ≃ selectedOriginal g I := by
  classical
  exact Equiv.ofBijective (fun i => ⟨g i.val,Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩) (by
    constructor
    · intro i j hij
      exact Subtype.ext (hg (congrArg Subtype.val hij))
    · intro j
      obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp j.property
      exact ⟨⟨i,hi⟩,Subtype.ext hij⟩)

def coefficientEquiv : (I →₀ ℤ) ≃ₗ[ℤ] (selectedOriginal g I →₀ ℤ) :=
  Finsupp.domLCongr (selectedEquiv g hg I)

include he in
omit [Fintype V] [Fintype W] [Fintype C] [Fintype D] in
theorem inverse_row_outside (r : Rows (C := C) (selectedOriginal g I)) :
    ∀ w ∈ I, e.symm r.val ≠ Sum.inl w := by
  classical
  intro w hw hh
  have hr : r.val = Sum.inl (g w) := by
    simpa only [Equiv.apply_symm_apply,he] using congrArg e hh
  exact r.property (g w) (Finset.mem_image.mpr ⟨w,hw,rfl⟩) hr

def rowMap : (Rows (C := D) I →₀ ℤ) →ₗ[ℤ] (Rows (C := C) (selectedOriginal g I) →₀ ℤ) where
  toFun x := Finsupp.equivFunOnFinite.symm
    (fun r => x ⟨e.symm r.val,inverse_row_outside g e he I r⟩)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

theorem rowMap_column (i : I) :
    rowMap g e he I (column (fun r w => B (e r) (g w)) I i) =
      column B (selectedOriginal g I) (selectedEquiv g hg I i) := by
  ext r
  change B (e (e.symm r.val)) (g i.val) = B r.val (g i.val)
  rw [Equiv.apply_symm_apply]

theorem maps_compatible :
    (rowMap g e he I).comp (selectedMap (fun r w => B (e r) (g w)) I) =
      (selectedMap B (selectedOriginal g I)).comp (coefficientEquiv g hg I).toLinearMap := by
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply,Finsupp.lsingle_apply,selectedMap,Finsupp.linearCombination_single,one_smul]
  rw [rowMap_column g hg e he B I]
  change _ = Finsupp.linearCombination ℤ (column B (selectedOriginal g I))
    (Finsupp.domLCongr (selectedEquiv g hg I) (Finsupp.single i 1))
  rw [Finsupp.domLCongr_single,Finsupp.linearCombination_single,one_smul]

include hg he in
theorem AS_transport (hAS : AS B (selectedOriginal g I)) : AS (fun r w => B (e r) (g w)) I := by
  obtain ⟨s,hs⟩ := Verification.PrimitiveLattice.primitive_columns_split_compatible _ hAS.1 hAS.2
  let t := (coefficientEquiv g hg I).symm.toLinearMap.comp
    ((LinearMap.fst ℤ _ _).comp (s.toLinearMap.comp (rowMap g e he I)))
  have ht : Function.LeftInverse t (selectedMap (fun r w => B (e r) (g w)) I) := by
    intro z
    change (coefficientEquiv g hg I).symm ((s (rowMap g e he I (selectedMap (fun r w => B (e r) (g w)) I z))).1) = z
    have hz := LinearMap.congr_fun (maps_compatible g hg e he B I) z
    change rowMap g e he I (selectedMap (fun r w => B (e r) (g w)) I z) =
      selectedMap B (selectedOriginal g I) (coefficientEquiv g hg I z) at hz
    rw [hz,hs]
    exact (coefficientEquiv g hg I).symm_apply_apply z
  exact ⟨ht.injective,Verification.CliqueSaturation.split_range_saturated _ _ ht⟩

#print axioms selectedOriginal
#print axioms selectedEquiv
#print axioms coefficientEquiv
#print axioms inverse_row_outside
#print axioms rowMap
#print axioms rowMap_column
#print axioms maps_compatible
#print axioms AS_transport
end Verification.FreezingASRows
