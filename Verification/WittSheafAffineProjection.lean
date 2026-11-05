/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WittSheafAffineInvariance
import Verification.PolynomialSectionIso

/-!
# Witt Sheaf Affine Projection

Polynomial zero evaluation is the inverse of ordinary Witt affine
invariance. Thus every actual affine-torus projection has its functorial
Witt pullback as a genuine ring isomorphism.
-/
noncomputable section
namespace Verification.WittSheafAffineProjection
open CategoryTheory AlgebraicGeometry Opposite
open Verification.WittSheafSectionsInput Verification.WittSheafAffineInvariance
variable (R : Type) [CommRing R] (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0})
variable (H : WittSheafAffineInvariance.Standard R W)
variable (S ι : Type) [CommRing S] [Algebra R S] [Fintype ι] (hs : Algebra.Smooth R S)

theorem polynomial_inverse (a : RingSection W (MvPolynomial ι S)) :
    (polynomialEquiv R W H S ι hs).symm a =
      pullback W (PolynomialSectionIso.zeroEvaluation R S ι).toRingHom a := by
  obtain ⟨a,rfl⟩ := (polynomialEquiv R W H S ι hs).surjective a
  rw [RingEquiv.symm_apply_apply]
  change a=pullback W (PolynomialSectionIso.zeroEvaluation R S ι).toRingHom (pullback W MvPolynomial.C a)
  rw [← RingHom.comp_apply,← pullback_comp]
  have h : (PolynomialSectionIso.zeroEvaluation R S ι).toRingHom.comp MvPolynomial.C=RingHom.id S := by
    ext s
    exact MvPolynomial.eval₂_C _ _ s
  rw [h,pullback_id]
  rfl

variable {U : Type} [CommRing U] [Algebra R U]
variable (e : U ≃ₐ[R] MvPolynomial ι S)

def equiv : RingSection W U ≃+* RingSection W S :=
  (ringEquiv W e.toRingEquiv).trans (polynomialEquiv R W H S ι hs).symm

theorem equiv_apply (a : RingSection W U) :
    equiv R W H S ι hs e a =
      pullback W ((PolynomialSectionIso.zeroEvaluation R S ι).comp e.toAlgHom).toRingHom a := by
  change (polynomialEquiv R W H S ι hs).symm (pullback W e.toRingHom a)=_
  rw [polynomial_inverse]
  exact (RingHom.congr_fun (pullback_comp W e.toRingHom
    (PolynomialSectionIso.zeroEvaluation R S ι).toRingHom) a).symm

#print axioms polynomial_inverse
#print axioms equiv
#print axioms equiv_apply
end Verification.WittSheafAffineProjection
