/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ContractionHomology
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.EuclideanDomain.Int

/-!
# Survivor Base Change

A basis of an integral idempotent's actual fixed module extends to every
commutative coefficient ring.  Rectangular integral inclusion/retraction
matrices are constructed from the basis; their identities survive coefficient
extension, including to the hyperbolic ring, without a flatness hypothesis.
-/

namespace Verification.SurvivorBaseChange

variable {R : Type*} [CommRing R]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Literal fixed vectors of a matrix. -/
def fixedModule (P : Matrix ι ι R) : Submodule R (ι → R) :=
  LinearMap.ker (Matrix.toLin' P - LinearMap.id)

theorem fixed_property (P : Matrix ι ι R) (x : fixedModule P) :
    Matrix.toLin' P x.val=x.val := sub_eq_zero.mp x.property

/-- An idempotent matrix gives an actual projection to its fixed submodule. -/
def projection (P : Matrix ι ι R) (hP : P*P=P) : (ι → R) →ₗ[R] fixedModule P where
  toFun x := ⟨Matrix.toLin' P x, by
    change Matrix.toLin' P (Matrix.toLin' P x)-Matrix.toLin' P x=0
    rw [← Matrix.toLin'_mul_apply, hP, sub_self]⟩
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul _ _ _

/-- The integral columns of a chosen survivor basis. -/
noncomputable def inclusionMatrix (P : Matrix ι ι R) (b : Basis κ R (fixedModule P)) :
    Matrix ι κ R :=
  LinearMap.toMatrix' ((fixedModule P).subtype.comp b.equivFun.symm.toLinearMap)

/-- The basis coordinates of the actual projection, defined on the whole ambient module. -/
noncomputable def retractionMatrix (P : Matrix ι ι R) (hP : P*P=P)
    (b : Basis κ R (fixedModule P)) : Matrix κ ι R :=
  LinearMap.toMatrix' (b.equivFun.toLinearMap.comp (projection P hP))

theorem inclusion_retraction (P : Matrix ι ι R) (hP : P*P=P)
    (b : Basis κ R (fixedModule P)) :
    inclusionMatrix P b * retractionMatrix P hP b = P := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul]
  simp only [inclusionMatrix, retractionMatrix, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  funext i
  change (b.equivFun.symm (b.equivFun (projection P hP x))).val i = _
  rw [b.equivFun.symm_apply_apply]
  rfl

theorem retraction_inclusion (P : Matrix ι ι R) (hP : P*P=P)
    (b : Basis κ R (fixedModule P)) :
    retractionMatrix P hP b * inclusionMatrix P b = 1 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_one]
  simp only [inclusionMatrix, retractionMatrix, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  change b.equivFun (projection P hP (b.equivFun.symm x).val)=x
  have he : projection P hP (b.equivFun.symm x).val=b.equivFun.symm x := by
    apply Subtype.ext
    exact fixed_property P _
  rw [he, b.equivFun.apply_symm_apply]

/-- Any pair of literal rectangular splitting matrices identifies the fixed module. -/
def splittingEquiv (P : Matrix ι ι R) (A : Matrix ι κ R) (B : Matrix κ ι R)
    (hAB : A*B=P) (hBA : B*A=1) : (κ → R) ≃ₗ[R] fixedModule P where
  toFun x := ⟨Matrix.toLin' A x, by
    change Matrix.toLin' P (Matrix.toLin' A x)-Matrix.toLin' A x=0
    rw [← Matrix.toLin'_mul_apply, ← hAB, Matrix.mul_assoc, hBA, Matrix.mul_one, sub_self]⟩
  invFun x := Matrix.toLin' B x.val
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul _ _ _
  left_inv x := by
    change Matrix.toLin' B (Matrix.toLin' A x)=x
    rw [← Matrix.toLin'_mul_apply, hBA, Matrix.toLin'_one, LinearMap.id_apply]
  right_inv x := by
    apply Subtype.ext
    change Matrix.toLin' A (Matrix.toLin' B x.val)=x.val
    rw [← Matrix.toLin'_mul_apply, hAB]
    exact fixed_property P x

/-- Every integral survivor basis extends to a basis equivalence over any ring. -/
noncomputable def scalarEquiv (P : Matrix ι ι ℤ) (hP : P*P=P)
    (b : Basis κ ℤ (fixedModule P)) :
    (κ → R) ≃ₗ[R] fixedModule (P.map (Int.castRingHom R)) :=
  splittingEquiv (P.map (Int.castRingHom R))
    ((inclusionMatrix P b).map (Int.castRingHom R))
    ((retractionMatrix P hP b).map (Int.castRingHom R))
    (by rw [← Matrix.map_mul, inclusion_retraction])
    (by rw [← Matrix.map_mul, retraction_inclusion]; simp)

/-- A literal finite free basis of the coefficient-extended fixed module. -/
noncomputable def scalarBasis (P : Matrix ι ι ℤ) (hP : P*P=P)
    (b : Basis κ ℤ (fixedModule P)) :
    Basis κ R (fixedModule (P.map (Int.castRingHom R))) :=
  (Pi.basisFun R κ).map (scalarEquiv P hP b)

open Verification.FinitePerturbation

/-- The matrix and linear-map survivor submodules are literally the same. -/
theorem fixedModule_pureProjection (U H : Matrix ι ι R) :
    fixedModule (pureProjection U H) =
      Verification.ContractionHomology.survivorModule (Matrix.toLin' U) (Matrix.toLin' H) := by
  simp only [fixedModule, Verification.ContractionHomology.survivorModule,
    pureProjection, map_sub, Matrix.toLin'_one, Matrix.toLin'_mul]
  rfl

/-- TF homology constructs an integral basis for the specified normalized survivor. -/
noncomputable def integralBasis (U H : Matrix ι ι ℤ)
    (hU : U*U=0) (hH : H*H=0) (hHUH : H*U*H=H) (hUHU : U*H*U=U)
    [NoZeroSMulDivisors ℤ (Verification.IntegralSplitting.Homology (Matrix.toLin' U))] :
    Basis (Fin (Module.finrank ℤ (Verification.IntegralSplitting.Homology (Matrix.toLin' U))))
      ℤ (fixedModule (pureProjection U H)) :=
  (Verification.ContractionHomology.survivorBasis (Matrix.toLin' U) (Matrix.toLin' H)
    (by simpa only [Matrix.toLin'_mul, map_zero] using congrArg Matrix.toLin' hU)
    (by simpa only [Matrix.toLin'_mul, map_zero] using congrArg Matrix.toLin' hH)
    (by simpa only [Matrix.toLin'_mul] using congrArg Matrix.toLin' hHUH)
    (by simpa only [Matrix.toLin'_mul] using congrArg Matrix.toLin' hUHU)).map
      (LinearEquiv.ofEq _ _ (fixedModule_pureProjection U H).symm)

/-- The resulting free survivor basis over every coefficient ring is constructed from TF. -/
noncomputable def tfScalarBasis (U H : Matrix ι ι ℤ)
    (hU : U*U=0) (hH : H*H=0) (hHUH : H*U*H=H) (hUHU : U*H*U=U)
    [NoZeroSMulDivisors ℤ (Verification.IntegralSplitting.Homology (Matrix.toLin' U))] :
    Basis (Fin (Module.finrank ℤ (Verification.IntegralSplitting.Homology (Matrix.toLin' U))))
      R (fixedModule ((pureProjection U H).map (Int.castRingHom R))) :=
  scalarBasis (pureProjection U H) (pureProjection_square U H hU hH hHUH hUHU)
    (integralBasis U H hU hH hHUH hUHU)

#print axioms fixedModule
#print axioms fixed_property
#print axioms projection
#print axioms inclusionMatrix
#print axioms retractionMatrix
#print axioms inclusion_retraction
#print axioms retraction_inclusion
#print axioms splittingEquiv
#print axioms scalarEquiv
#print axioms scalarBasis
#print axioms fixedModule_pureProjection
#print axioms integralBasis
#print axioms tfScalarBasis

end Verification.SurvivorBaseChange
