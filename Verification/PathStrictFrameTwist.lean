/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathStrictCoefficientAction
import Verification.PathActualFrameTwist
import Verification.PathMatrixCoefficientGrading

/-!
# Path Strict Frame Twist

The four-periodic path frame change is an actual involutive strict-sheaf scalar isomorphism. Its conjugation removes the original-normal factor in every homogeneous full-rho arrow.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathStrictFrameTwist
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.PathGradedCoefficientAction
open Verification.GradedMilnorWittDegreeSpaces
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (P : GradedMilnorWittHomogeneity.Standard site N W)
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (H : GradedMilnorWittStrictScalars.Standard J L G R site M N W P V)


open Classical Verification.PathCoefficientGrading
local notation "DR" => (W.symbols (CommRingCat.of R)).toCoefficients
local notation "factor" => PathNormalSignTwist.factor PathCoefficientRing.g (fun j=>j/2)

theorem factor_degree (I : Finset ℕ) : Homogeneous 0 (factor I) := by
  induction I using Finset.induction_on with
  | empty => simpa only [PathNormalSignTwist.factor,Finset.prod_empty] using homogeneous_one
  | @insert i I hi ih =>
    rw [PathNormalSignTwist.factor_insert _ _ I i hi]
    have h := PathMatrixCoefficientGrading.power PathCoefficientRing.g 0 homogeneous_g (i/2)
    simpa only [mul_zero,zero_add] using homogeneous_mul h ih

def realized {q : ℤ} (c : PathCoefficientRing.Coeff) (hc : Homogeneous q c) :
    space site N W (CommRingCat.of R) q :=
  ⟨PathMilnorWittCoefficients.realize DR c,PathMilnorWittGradedRealization.homogeneous P (CommRingCat.of R) hc⟩

def factorPiece (I : Finset ℕ) (k : ℤ) : space site N W (CommRingCat.of R) (k-k) :=
  realized R site N W P (factor I) (by simpa only [sub_self] using factor_degree I)

def twist (I : Finset ℕ) (k : ℤ) : M k ≅ M k where
  hom := H.scalar k k (factorPiece R site N W P I k)
  inv := H.scalar k k (factorPiece R site N W P I k)
  hom_inv_id := by
    rw [H.scalar_comp]
    have he : GradedMilnorWittStrictScalars.product R site N W P k k k
      (factorPiece R site N W P I k) (factorPiece R site N W P I k)=
      GradedMilnorWittStrictScalars.one R site N W P k := by
      apply Subtype.ext
      change PathMilnorWittCoefficients.realize DR (factor I)*PathMilnorWittCoefficients.realize DR (factor I)=1
      rw [←map_mul,PathNormalSignTwist.factor_square _ _ PathCoefficientRing.g_square,map_one]
    rw [he,H.scalar_one]
  inv_hom_id := by
    rw [H.scalar_comp]
    have he : GradedMilnorWittStrictScalars.product R site N W P k k k
      (factorPiece R site N W P I k) (factorPiece R site N W P I k)=
      GradedMilnorWittStrictScalars.one R site N W P k := by
      apply Subtype.ext
      change PathMilnorWittCoefficients.realize DR (factor I)*PathMilnorWittCoefficients.realize DR (factor I)=1
      rw [←map_mul,PathNormalSignTwist.factor_square _ _ PathCoefficientRing.g_square,map_one]
    rw [he,H.scalar_one]

theorem signed_degree (j : ℕ) {q : ℤ} {c : PathCoefficientRing.Coeff} (hc : Homogeneous q c) :
    Homogeneous q (PathCoefficientRing.g^(j/2)*c) := by
  have h := PathMatrixCoefficientGrading.power PathCoefficientRing.g 0 homogeneous_g (j/2)
  simpa only [mul_zero,zero_add] using homogeneous_mul h hc

omit [J.Additive] [L.Additive] in
theorem conjugate (I : Finset ℕ) (j : ℕ) (hj : j∉I) (k l : ℤ)
    (c : PathCoefficientRing.Coeff) (hc : Homogeneous (l-k) c) :
    (twist J L G R site M N W P V H (insert j I) k).hom ≫
      H.scalar k l (realized R site N W P (PathCoefficientRing.g^(j/2)*c) (signed_degree j hc)) ≫
      (twist J L G R site M N W P V H I l).hom=
    H.scalar k l (realized R site N W P c hc) := by
  change H.scalar k k _ ≫ H.scalar k l _ ≫ H.scalar l l _ = _
  rw [H.scalar_comp,H.scalar_comp]
  congr 1
  apply Subtype.ext
  change PathMilnorWittCoefficients.realize DR (factor (insert j I)) *
    (PathMilnorWittCoefficients.realize DR (PathCoefficientRing.g^(j/2)*c)*
      PathMilnorWittCoefficients.realize DR (factor I)) = PathMilnorWittCoefficients.realize DR c
  simpa only [PathActualFrameTwist.factor,map_mul,map_pow,PathMilnorWittCoefficients.realize_g,mul_one] using
    PathActualFrameTwist.adjacent DR I j hj c 1

#print axioms factor_degree
#print axioms realized
#print axioms factorPiece
#print axioms twist
#print axioms signed_degree
#print axioms conjugate
end Verification.PathStrictFrameTwist
