/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizationQuotient
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Quotient Away Algebra

The literal quotient of a principal localization is the principal
localization of the quotient. The equivalence preserves the base algebra
and its full square of quotient/localization maps.
-/
noncomputable section
namespace Verification.QuotientAwayAlgebra
variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
variable (I : Ideal A) (z : A)
open Verification.LocalizationQuotient

instance imagePowersLocalization : IsLocalization.Away (Ideal.Quotient.mk I z)
    (LocalizedQuotient I (Submonoid.powers z)) := by
  simpa only [quotientMonoid, Submonoid.map_powers] using
    (inferInstance : IsLocalization (quotientMonoid I (Submonoid.powers z))
      (LocalizedQuotient I (Submonoid.powers z)))

def imageEquiv : LocalizedQuotient I (Submonoid.powers z) ≃ₐ[A ⧸ I]
    Localization.Away (Ideal.Quotient.mk I z) :=
  IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I z)) _ _

def ringEquiv : QuotientLocalized I (Submonoid.powers z) ≃+*
    Localization.Away (Ideal.Quotient.mk I z) :=
  (quotientLocalizationEquiv I (Submonoid.powers z)).trans (imageEquiv A I z).toRingEquiv

theorem ringEquiv_generator (a : A) :
    ringEquiv A I z (Ideal.Quotient.mk (localizedIdeal I (Submonoid.powers z))
      (algebraMap A (Localization.Away z) a)) =
      algebraMap (A ⧸ I) (Localization.Away (Ideal.Quotient.mk I z)) (Ideal.Quotient.mk I a) := by
  change imageEquiv A I z (forward I (Submonoid.powers z)
    (Ideal.Quotient.mk _ (algebraMap A (Localization.Away z) a))) = _
  rw [forward_generator]
  exact (imageEquiv A I z).commutes _

def equiv : QuotientLocalized I (Submonoid.powers z) ≃ₐ[R]
    Localization.Away (Ideal.Quotient.mk I z) :=
  AlgEquiv.ofRingEquiv (f := ringEquiv A I z) (fun r => by
    exact ringEquiv_generator A I z (algebraMap R A r))

theorem equiv_generator (a : A) :
    equiv R A I z (Ideal.Quotient.mk (localizedIdeal I (Submonoid.powers z))
      (algebraMap A (Localization.Away z) a)) =
      algebraMap (A ⧸ I) (Localization.Away (Ideal.Quotient.mk I z)) (Ideal.Quotient.mk I a) :=
  ringEquiv_generator A I z a

theorem quotient_localization_square :
    (equiv R A I z).toAlgHom.comp (Ideal.Quotient.mkₐ R (localizedIdeal I (Submonoid.powers z))) =
      IsLocalization.liftAlgHom (M := Submonoid.powers z)
        (f := (IsScalarTower.toAlgHom R (A ⧸ I) (Localization.Away (Ideal.Quotient.mk I z))).comp
          (Ideal.Quotient.mkₐ R I)) (by
          intro m
          obtain ⟨n,hn⟩ := m.property
          change IsUnit (algebraMap (A ⧸ I) _ (Ideal.Quotient.mk I m.val))
          rw [← hn, map_pow, map_pow]
          exact (IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk I z)).pow n) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers z)
  ext a
  change equiv R A I z (Ideal.Quotient.mk _ (algebraMap A (Localization.Away z) a)) = _
  rw [equiv_generator]
  symm
  exact IsLocalization.lift_eq _ a

#print axioms imagePowersLocalization
#print axioms imageEquiv
#print axioms ringEquiv
#print axioms ringEquiv_generator
#print axioms equiv
#print axioms equiv_generator
#print axioms quotient_localization_square
end Verification.QuotientAwayAlgebra
