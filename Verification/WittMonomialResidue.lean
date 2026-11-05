/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WittSheafLaurentResidue
import Verification.WittSheafAffineInvariance

/-!
# Witt Monomial Residue

The genuine Laurent contraction on a monomial whose actual unit
factorization has been proved. Both coefficient transports are functorial
pullbacks, and the residual parity is derived from ordinary normalization.
-/
noncomputable section
namespace Verification.WittMonomialResidue
open CategoryTheory AlgebraicGeometry Opposite
open Verification.WittSheafSectionsInput
variable (R : Type) [CommRing R] (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0})

theorem pullback_coefficient {S T : Type} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (a : RingSection W R) :
    pullback W f.toRingHom (pullback W (algebraMap R S) a)=pullback W (algebraMap R T) a := by
  have h : f.toRingHom.comp (algebraMap R S)=algebraMap R T := by
    ext r
    exact f.commutes r
  rw [← RingHom.comp_apply,← WittSheafAffineInvariance.pullback_comp,h]

variable (D : Symbols R W) (site : GrothendieckTopology Scheme.{0})
variable (N : ℤ → Sheaf site (ModuleCat.{0} ℤ)) (E : Comparison R W site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (Norm : LaurentNormalization R W D site N E K)
variable {U V S : Type} [CommRing U] [CommRing V] [CommRing S]
variable [Algebra R U] [Algebra R V] [Algebra R S]
variable (hu : Algebra.Smooth R U) (hv : Algebra.Smooth R V) (hs : Algebra.Smooth R S)
variable (f : U →ₐ[R] LaurentBasepoint.Laurent S) (g : V →ₐ[R] S)

theorem pullback_monomial (u : Uˣ) (w : Vˣ) (n : ℕ)
    (h : Units.map f.toRingHom.toMonoidHom u =
      LaurentPolynomialUniversal.parameterUnit S ^ n *
        Units.map (LaurentBasepoint.coefficient R S).toRingHom.toMonoidHom
          (Units.map g.toRingHom.toMonoidHom w)) (a : RingSection W R) :
    pullback W f.toRingHom (form R W D U hu u * pullback W (algebraMap R U) a) =
      (form R W D (LaurentBasepoint.Laurent S) (WittSheafLaurentResidue.laurentSmooth R S hs)
        (LaurentPolynomialUniversal.parameterUnit S))^n *
      pullback W (LaurentBasepoint.coefficient R S).toRingHom
        (pullback W g.toRingHom (form R W D V hv w * pullback W (algebraMap R V) a)) := by
  rw [map_mul,form_natural R W D U _ hu (WittSheafLaurentResidue.laurentSmooth R S hs),
    h,map_mul,map_pow,← form_natural R W D S _ hs (WittSheafLaurentResidue.laurentSmooth R S hs),
    ← form_natural R W D V S hv hs]
  rw [map_mul,map_mul,mul_assoc]
  congr 1
  congr 1
  rw [pullback_coefficient R W f,pullback_coefficient R W g,
    pullback_coefficient R W (LaurentBasepoint.coefficient R S)]

include Norm in
theorem residue (u : Uˣ) (w : Vˣ) (n : ℕ)
    (h : Units.map f.toRingHom.toMonoidHom u =
      LaurentPolynomialUniversal.parameterUnit S ^ n *
        Units.map (LaurentBasepoint.coefficient R S).toRingHom.toMonoidHom
          (Units.map g.toRingHom.toMonoidHom w)) (q : ℤ) (a : RingSection W R) :
    WittSheafLaurentResidue.residue R W site N E K S hs q
      (pullback W f.toRingHom (form R W D U hu u * pullback W (algebraMap R U) a)) =
        if n%2=0 then 0 else
          pullback W g.toRingHom (form R W D V hv w * pullback W (algebraMap R V) a) := by
  rw [pullback_monomial R W D hu hv hs f g u w n h a]
  exact WittSheafLaurentResidue.residue_parity R W D site N E K Norm S hs q _ n

#print axioms pullback_coefficient
#print axioms pullback_monomial
#print axioms residue
end Verification.WittMonomialResidue
