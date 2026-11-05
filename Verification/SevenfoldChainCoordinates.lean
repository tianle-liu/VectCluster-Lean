/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SevenfoldChainMatrix

/-!
# Sevenfold Chain Coordinates

Zero-extension of actual induced-simplex coefficients gives literal
coordinates in the ten-face boundary matrix. The matrix compatibility
is proved for every induced vertex subset.
-/
noncomputable section
open scoped Classical
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.SevenfoldChainCoordinates
open Verification.SevenfoldGraphFreeness Verification.SevenfoldChainIndex
open Verification.SevenfoldChainMatrix Verification.GraphCover Verification.GraphChainMatrix
variable (T : Finset (Fin 5))

def extend : (Simplex graph T → ℤ) →ₗ[ℤ] (Fin 10 → ℤ) where
  toFun f i := if h : face i ⊆ T then f (index T ⟨i,h⟩) else 0
  map_add' f g := by funext i; by_cases h : face i ⊆ T <;> simp [h]
  map_smul' r f := by funext i; by_cases h : face i ⊆ T <;> simp [h]

theorem extend_index (f : Simplex graph T → ℤ) (i : {i : Fin 10 // face i ⊆ T}) :
    extend T f i.val = f (index T i) := by simp [extend,i.property]

theorem extend_injective : Function.Injective (extend T) := by
  intro f g h
  funext J
  obtain ⟨i,rfl⟩ := (index T).surjective J
  have hh := congrFun h i.val
  simpa only [extend_index] using hh

theorem sum_extend (f : Simplex graph T → ℤ) :
    ∑ i : Fin 10, extend T f i = ∑ J : Simplex graph T, f J := by
  symm
  apply Fintype.sum_of_injective (fun J : Simplex graph T => ((index T).symm J).val)
    (Subtype.val_injective.comp (index T).symm.injective)
  · intro i hi
    by_cases h : face i ⊆ T
    · exact False.elim (hi ⟨index T ⟨i,h⟩,by simp⟩)
    · simp [extend,h]
  · intro J
    rw [extend_index,Equiv.apply_symm_apply]

theorem matrix_support : ∀ i j : Fin 10, matrix i j ≠ 0 → face i ⊆ face j := by decide

theorem boundary (f : Simplex graph T → ℤ) :
    extend T ((chainMatrix (R := ℤ) graph T).mulVec f) = Matrix.mulVec matrix (extend T f) := by
  funext i
  by_cases hi : face i ⊆ T
  · change (if h : face i ⊆ T then _ else 0) = _
    rw [dif_pos hi]
    change (∑ J : Simplex graph T, chainMatrix (R := ℤ) graph T (index T ⟨i,hi⟩) J * f J) = _
    rw [← sum_extend]
    change (∑ j : Fin 10, _) = ∑ j : Fin 10, matrix i j * extend T f j
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : face j ⊆ T
    · simp only [extend,LinearMap.coe_mk,AddHom.coe_mk,dif_pos hj,entry]
    · simp only [extend,LinearMap.coe_mk,AddHom.coe_mk,dif_neg hj,mul_zero]
  · change (if h : face i ⊆ T then _ else 0) = _
    rw [dif_neg hi]
    symm
    change (∑ j : Fin 10, matrix i j * extend T f j) = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hm : matrix i j=0
    · rw [hm,zero_mul]
    · have hj : ¬face j ⊆ T := fun h => hi ((matrix_support i j hm).trans h)
      simp [extend,hj]

#print axioms extend
#print axioms extend_index
#print axioms extend_injective
#print axioms sum_extend
#print axioms matrix_support
#print axioms boundary
end Verification.SevenfoldChainCoordinates
