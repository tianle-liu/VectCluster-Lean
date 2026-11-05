/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineCoefficientSectionIso
import Verification.GradedMilnorWittDegreewiseEquiv
import Verification.SheafSectionDegreeTransport

/-!
# Affine Coefficient Section Total

The canonical zero section of any actual affine-space presentation
is an isomorphism on total MW sections. Any constructed algebra section
of it induces the inverse, by the established ordinary affine invariance.
-/
noncomputable section
namespace Verification.AffineCoefficientSectionTotal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R S T ν : Type) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Fintype ν]
variable (e : S ≃ₐ[R] MvPolynomial ν T)
variable (hs : Algebra.Smooth R S) (ht : Algebra.Smooth R T)
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)

def degreeEquiv (q : ℤ) : SheafGradedLaurentResidue.Section site N S q ≃+
    SheafGradedLaurentResidue.Section site N T q :=
  SheafSectionDegreeTransport.equiv site N (by omega : q-(0:ℕ)=q)
    (AffineCoefficientSectionIso.sections J L G R S T ν (Fin 0) e hs ht H 0 (Fintype.card_fin 0) site M N V q)

include hV in
omit [J.Additive] [L.Additive] [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
  [J.CommShift ℤ] [L.CommShift ℤ] [HasShift D ℤ] in
theorem degree_apply (q : ℤ) (a : SheafGradedLaurentResidue.Section site N S q) :
    degreeEquiv J L G R S T ν e hs ht H site M N V q a=
      ActualSheafContractionRestriction.pullback site (N q)
        (AffineCoefficientSectionIso.sectionMap R S T ν e).toRingHom a :=
  SheafSectionDegreeTransport.apply_eq site N (by omega : q-(0:ℕ)=q)
    (AffineCoefficientSectionIso.sections J L G R S T ν (Fin 0) e hs ht H 0 (Fintype.card_fin 0) site M N V q)
    (AffineCoefficientSectionIso.sectionMap R S T ν e).toRingHom
    (AffineCoefficientSectionIso.sections_apply J L G R S T ν (Fin 0) e hs ht H 0 (Fintype.card_fin 0)
      site M N V hV q) a

variable (W : GradedMilnorWittSheaf.Standard site N)

def totalEquiv : W.Total (CommRingCat.of S) ≃+* W.Total (CommRingCat.of T) :=
  GradedMilnorWittDegreewiseEquiv.equiv site N W
    (degreeEquiv J L G R S T ν e hs ht H site M N V)
    (AffineCoefficientSectionIso.sectionMap R S T ν e).toRingHom
    (degree_apply J L G R S T ν e hs ht H site M N V hV)

omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem total_apply (a : W.Total (CommRingCat.of S)) :
    totalEquiv J L G R S T ν e hs ht H site M N V hV W a=
      GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of S) (T:=CommRingCat.of T)
        (AffineCoefficientSectionIso.sectionMap R S T ν e).toRingHom a := rfl

omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem inverse_section (s : T →ₐ[R] S)
    (hp : (AffineCoefficientSectionIso.sectionMap R S T ν e).comp s=AlgHom.id R T)
    (a : W.Total (CommRingCat.of T)) :
    (totalEquiv J L G R S T ν e hs ht H site M N V hV W).symm a=
      GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of T) (T:=CommRingCat.of S) s.toRingHom a := by
  apply (totalEquiv J L G R S T ν e hs ht H site M N V hV W).injective
  rw [RingEquiv.apply_symm_apply,total_apply]
  have he : (AffineCoefficientSectionIso.sectionMap R S T ν e).toRingHom.comp s.toRingHom=RingHom.id T :=
    congrArg AlgHom.toRingHom hp
  rw [←RingHom.comp_apply,←GradedMilnorWittSheaf.pullback_comp,he,GradedMilnorWittSheaf.pullback_id]
  rfl

#print axioms degreeEquiv
#print axioms degree_apply
#print axioms totalEquiv
#print axioms total_apply
#print axioms inverse_section
end Verification.AffineCoefficientSectionTotal
