/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineShiftedThomNaturality
import Verification.LocalizedAffineThomInvariance
import Verification.AffineSectionTransport

/-!
# Affine Coefficient Section Iso

The actual zero section of any affine-space coordinate presentation
induces an isomorphism on coefficient sections. Its map is identified
with the ordinary sheaf pullback using uniform affine invariance and
Thom representability, with no separate cohomology assumption.
-/
noncomputable section
namespace Verification.AffineCoefficientSectionIso
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R S T ν μ : Type) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Fintype ν] [Fintype μ] [LinearOrder μ]
variable (e : S ≃ₐ[R] MvPolynomial ν T)
variable (hs : Algebra.Smooth R S) (ht : Algebra.Smooth R T)
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (r : ℕ) (hr : Fintype.card μ = r)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
local notation "F" => AffineRelativeThom.theory R μ G
local notation "Fₗ" => AffineRelativeThom.theory R μ G ⋙ DerivedCategory.Q ⋙ L

def sectionMap : S →ₐ[R] T := (PolynomialSectionIso.zeroEvaluation R T ν).comp e.toAlgHom

def theoryIso : (Fₗ).obj (op (CommRingCat.mkUnder (CommRingCat.of R) T)) ≅
    (Fₗ).obj (op (CommRingCat.mkUnder (CommRingCat.of R) S)) := by
  letI : IsIso (PolynomialSectionIso.projectionMap R T ν Fₗ) := H.projection T μ ν ht
  exact AffineSectionTransport.sectionIso R T ν S e Fₗ

omit [J.Additive] [L.Additive] [J.CommShift ℤ] [L.CommShift ℤ]
  [Preadditive D] [HasShift D ℤ] [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [LinearOrder μ] in
theorem theoryIso_hom : (theoryIso L G R S T ν μ e ht H).hom =
    (Fₗ).map (sectionMap R S T ν e).toUnder.op := by
  letI : IsIso (PolynomialSectionIso.projectionMap R T ν Fₗ) := H.projection T μ ν ht
  exact AffineSectionTransport.sectionIso_hom R T ν S e Fₗ

def sections (j : ℤ) :
    (N (j-r)).val.obj (op (Spec (CommRingCat.of S))) ≃+
    (N (j-r)).val.obj (op (Spec (CommRingCat.of T))) :=
  (AffineShiftedThomSections.evaluate J L G R S μ r hr site M N V hs j).symm.trans
    ((LocalizedThomSections.precompose (theoryIso L G R S T ν μ e ht H).symm).trans
      (AffineShiftedThomSections.evaluate J L G R T μ r hr site M N V ht j))

include hV in
omit [J.Additive] [L.Additive] [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
  [J.CommShift ℤ] [L.CommShift ℤ] [HasShift D ℤ] in
theorem sections_apply (j : ℤ) (a : (N (j-r)).val.obj (op (Spec (CommRingCat.of S)))) :
    sections J L G R S T ν μ e hs ht H r hr site M N V j a =
    (N (j-r)).val.map (Spec.map (CommRingCat.ofHom (sectionMap R S T ν e).toRingHom)).op a := by
  change AffineShiftedThomSections.evaluate J L G R T μ r hr site M N V ht j
    ((theoryIso L G R S T ν μ e ht H).hom ≫
      (AffineShiftedThomSections.evaluate J L G R S μ r hr site M N V hs j).symm a) = _
  rw [theoryIso_hom]
  have h := AffineShiftedThomNaturality.evaluate_naturality J L G R S T μ r hr
    (sectionMap R S T ν e) site M N V hV hs ht j
    ((AffineShiftedThomSections.evaluate J L G R S μ r hr site M N V hs j).symm a)
  simpa only [AddEquiv.apply_symm_apply] using h

#print axioms sectionMap
#print axioms theoryIso
#print axioms theoryIso_hom
#print axioms sections
#print axioms sections_apply
end Verification.AffineCoefficientSectionIso
