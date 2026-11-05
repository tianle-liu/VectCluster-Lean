/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.DegreeBasisCoordinates

/-!
# Degree Matrix Cutout

A homogeneous matrix restricted to two actual degrees has precisely the
columns extracted using the proved degree-index bijections.
-/

namespace Verification.DegreeMatrixCutout

open Classical Verification.GradedPerturbation Verification.DegreeBasisCoordinates

variable {R : Type*} [CommRing R]
variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

noncomputable def columns (D : Matrix ι ι R) (a : α → ι) (b : β → ι) :
    (α →₀ R) →ₗ[R] (β →₀ R) :=
  Finsupp.linearCombination R (fun x => Finsupp.equivFunOnFinite.symm (fun y => D (b y) (a x)))

theorem coordinate_cutout (d : ι → ℤ) (D : Matrix ι ι R) (k : ℤ)
    (hd : Homogeneous d k D) (p q : ℤ) (hpq : q=p+k)
    (a : α ≃ {i // d i=p}) (b : β ≃ {i // d i=q}) :
    (basisEquiv d q b).toLinearMap.comp
      ((matrixDegreeMap d D k hd p q hpq).comp (basisEquiv d p a).symm.toLinearMap)=
        columns D (fun x => (a x).val) (fun y => (b y).val) := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro r
  apply Finsupp.ext
  intro y
  simp only [LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,Finsupp.lsingle_apply]
  rw [basis_apply]
  change (Matrix.mulVec D ((basisEquiv d p a).symm (Finsupp.single x r)).val) (b y).val = _
  rw [basis_inverse_single,Matrix.mulVec_single]
  simp only [columns,Finsupp.linearCombination_single,Finsupp.smul_apply,
    smul_eq_mul]
  exact mul_comm _ _

#print axioms columns
#print axioms coordinate_cutout

end Verification.DegreeMatrixCutout
