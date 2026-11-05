/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathStrictCoefficientAction

/-!
# Graded Scalar Degree Transport

Ordinary scalar morphisms respect equality transport of both degrees.
-/
noncomputable section
namespace Verification.GradedScalarDegreeTransport
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

omit [J.Additive] [L.Additive] in
theorem scalar (s t s' t' : ℤ) (hs : s=s') (ht : t'=t)
    (c : space site N W (CommRingCat.of R) (t'-s'))
    (c' : space site N W (CommRingCat.of R) (t-s)) (hc : c.val=c'.val) :
    eqToHom (congrArg M hs) ≫ H.scalar s' t' c ≫ eqToHom (congrArg M ht)=H.scalar s t c' := by
  subst s' t'
  have he : c=c' := Subtype.ext hc
  subst c
  simp
#print axioms scalar
end Verification.GradedScalarDegreeTransport
