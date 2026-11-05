/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathConeCoefficients
import Verification.GradedPerturbation

/-!
# Matrix Of Degree

Degree and intertwining statements for two actual finite coefficient
systems of the same linear operator.
-/

namespace Verification.MatrixOfDegree

open Verification.PathEndpointCoordinates Verification.PathConeCoefficients Verification.GradedPerturbation

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
theorem matrixOf_degree (d : ι → ℤ) (E : M ≃ₗ[R] (ι → R)) (D : M →ₗ[R] M)
    (h : ∀ p x, E x ∈ degreeModule d p → E (D x) ∈ degreeModule d (p+1)) :
    Homogeneous d 1 (matrixOf E D) := by
  intro y x hxy
  let f : ι → R := Pi.single x 1
  have hf : f ∈ degreeModule d (d x) := by
    intro i hi
    have hn : i ≠ x := fun he => hi (congrArg d he)
    exact Pi.single_eq_of_ne hn 1
  have hh := h (d x) (E.symm f) (by simpa only [LinearEquiv.apply_symm_apply] using hf) y hxy
  simp only [matrixOf,LinearMap.toMatrix'_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun j : ι => if j=x then (1:R) else 0)=f by
    funext j; simp [f,Pi.single_apply,eq_comm]]
  exact hh

/-- The finite basis change intertwines the two independently transported matrices. -/
theorem coefficient_intertwining (E : M ≃ₗ[R] (ι → R)) (F : M ≃ₗ[R] (κ → R)) (D : M →ₗ[R] M) :
    (Matrix.toLin' (matrixOf F D)).comp (E.symm.trans F).toLinearMap=
      (E.symm.trans F).toLinearMap.comp (Matrix.toLin' (matrixOf E D)) := by
  apply LinearMap.ext
  intro x
  change (matrixOf F D).mulVec (F (E.symm x))=F (E.symm ((matrixOf E D).mulVec x))
  rw [matrixOf_mulVec,matrixOf_mulVec,LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]

structure ChangeData (A : Matrix ι ι R) (B : Matrix κ κ R) where
  change : (ι → R) ≃ₗ[R] (κ → R)
  intertwining : (Matrix.toLin' B).comp change.toLinearMap=change.toLinearMap.comp (Matrix.toLin' A)

noncomputable def changeData (E : M ≃ₗ[R] (ι → R)) (F : M ≃ₗ[R] (κ → R)) (D : M →ₗ[R] M) :
    ChangeData (matrixOf E D) (matrixOf F D) where
  change := E.symm.trans F
  intertwining := coefficient_intertwining E F D

#print axioms matrixOf_degree
#print axioms coefficient_intertwining
#print axioms ChangeData
#print axioms changeData

end Verification.MatrixOfDegree
