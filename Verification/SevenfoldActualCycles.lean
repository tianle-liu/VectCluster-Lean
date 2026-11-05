/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SevenfoldCycleSupport
import Verification.PerturbedHomologyModel

/-!
# Sevenfold Actual Cycles

The kernel identification uses the genuine chain differential, transported
through the actual induced-simplex coordinates.
-/
noncomputable section
open scoped Classical
set_option maxHeartbeats 1600000
namespace Verification.SevenfoldActualCycles
open Verification.SevenfoldGraphFreeness Verification.SevenfoldChainCoordinates
open Verification.SevenfoldChainDegrees Verification.GradedPerturbation
open Verification.GraphCoverGrading Verification.GraphChainMatrix
variable (T : Finset (Fin 5))

def delta : degreeModule (R := ℤ) (degree graph T) (-2) →ₗ[ℤ]
    degreeModule (R := ℤ) (degree graph T) (-1) :=
  matrixDegreeMap _ (chainMatrix graph T) 1 (chainMatrix_degree graph T) (-2) (-1) (by decide)

def coordinateDelta : coordinates T (-2) →ₗ[ℤ] (Fin 10 → ℤ) :=
  (Matrix.toLin' SevenfoldChainMatrix.matrix).comp (coordinates T (-2)).subtype

def kernelEquiv : LinearMap.ker (delta T) ≃ₗ[ℤ] LinearMap.ker (coordinateDelta T) where
  toFun f := ⟨term T (-2) f.val,by
    change Matrix.mulVec SevenfoldChainMatrix.matrix (extend T f.val.val)=0
    rw [← boundary]
    have hf : (chainMatrix graph T).mulVec f.val.val=0 :=
      congrArg Subtype.val f.property
    rw [hf,map_zero]⟩
  invFun x := ⟨(term T (-2)).symm x.val,by
    apply Subtype.ext
    change (chainMatrix graph T).mulVec ((term T (-2)).symm x.val).val=0
    apply extend_injective T
    rw [boundary,map_zero]
    have he : extend T ((term T (-2)).symm x.val).val=x.val.val :=
      congrArg Subtype.val ((term T (-2)).apply_symm_apply x.val)
    rw [he]
    exact x.property⟩
  left_inv f := by apply Subtype.ext; exact (term T (-2)).symm_apply_apply f.val
  right_inv x := by apply Subtype.ext; exact (term T (-2)).apply_symm_apply x.val
  map_add' f g := by apply Subtype.ext; exact map_add (term T (-2)) f.val g.val
  map_smul' r f := by apply Subtype.ext; exact map_smul (term T (-2)) r f.val

theorem term_minus_three : Subsingleton (degreeModule (R := ℤ) (degree graph T) (-3)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  apply Subtype.ext
  funext I
  apply x.property
  have hc := independent_card I.val I.property.2
  change -(I.val.card : ℤ) ≠ -3
  omega

#print axioms delta
#print axioms coordinateDelta
#print axioms kernelEquiv
#print axioms term_minus_three
end Verification.SevenfoldActualCycles
