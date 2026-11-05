/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Localization Quotient

Quotients and localizations commute through their actual universal maps.
This is used to pass from a globally presented exchange algebra to its
locally closed zero strata, without identifying rings only on field points.
-/
namespace Verification.LocalizationQuotient
variable {R : Type*} [CommRing R] (I : Ideal R) (M : Submonoid R)

abbrev localizedIdeal : Ideal (Localization M) := I.map (algebraMap R (Localization M))
abbrev quotientMonoid : Submonoid (R ⧸ I) := M.map (Ideal.Quotient.mk I)
abbrev LocalizedQuotient := Localization (quotientMonoid I M)
abbrev QuotientLocalized := Localization M ⧸ localizedIdeal I M

def baseToLocalizedQuotient : R →+* LocalizedQuotient I M :=
  (algebraMap (R ⧸ I) _).comp (Ideal.Quotient.mk I)

theorem baseToLocalizedQuotient_units (m : M) : IsUnit (baseToLocalizedQuotient I M m) := by
  exact IsLocalization.map_units (LocalizedQuotient I M)
    ⟨Ideal.Quotient.mk I m, Submonoid.mem_map_of_mem _ m.property⟩

noncomputable def localizationMap : Localization M →+* LocalizedQuotient I M :=
  IsLocalization.lift (baseToLocalizedQuotient_units I M)

theorem localizationMap_kills : localizedIdeal I M ≤ RingHom.ker (localizationMap I M) := by
  rw [localizedIdeal, Ideal.map_le_iff_le_comap]
  intro r hr
  change localizationMap I M (algebraMap R _ r) = 0
  rw [localizationMap, IsLocalization.lift_eq]
  change algebraMap (R ⧸ I) _ (Ideal.Quotient.mk I r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

noncomputable def forward : QuotientLocalized I M →+* LocalizedQuotient I M :=
  Ideal.Quotient.lift _ (localizationMap I M) (localizationMap_kills I M)

def baseToQuotientLocalized : R →+* QuotientLocalized I M :=
  (Ideal.Quotient.mk (localizedIdeal I M)).comp (algebraMap R (Localization M))

theorem baseToQuotientLocalized_kills : I ≤ RingHom.ker (baseToQuotientLocalized I M) := by
  intro r hr
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_map_of_mem (algebraMap R (Localization M)) hr

def quotientMap : (R ⧸ I) →+* QuotientLocalized I M :=
  Ideal.Quotient.lift _ (baseToQuotientLocalized I M) (baseToQuotientLocalized_kills I M)

theorem quotientMap_units (m : quotientMonoid I M) : IsUnit (quotientMap I M m) := by
  obtain ⟨r,hr,he⟩ := m.property
  have h : (m : R ⧸ I) = Ideal.Quotient.mk I r := he.symm
  rw [h]
  change IsUnit (Ideal.Quotient.mk (localizedIdeal I M) (algebraMap R (Localization M) r))
  exact (IsLocalization.map_units (Localization M) (⟨r,hr⟩ : M)).map (Ideal.Quotient.mk _)

noncomputable def backward : LocalizedQuotient I M →+* QuotientLocalized I M :=
  IsLocalization.lift (quotientMap_units I M)

theorem forward_generator (r : R) :
    forward I M (Ideal.Quotient.mk (localizedIdeal I M) (algebraMap R (Localization M) r)) =
      algebraMap (R ⧸ I) (LocalizedQuotient I M) (Ideal.Quotient.mk I r) := by
  change IsLocalization.lift (baseToLocalizedQuotient_units I M)
    (algebraMap R (Localization M) r) = _
  rw [IsLocalization.lift_eq]
  rfl

theorem backward_generator (r : R) :
    backward I M (algebraMap (R ⧸ I) (LocalizedQuotient I M) (Ideal.Quotient.mk I r)) =
      Ideal.Quotient.mk (localizedIdeal I M) (algebraMap R (Localization M) r) := by
  rw [backward, IsLocalization.lift_eq]
  rfl

theorem backward_forward : (backward I M).comp (forward I M) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext M
  ext r
  change backward I M (forward I M (Ideal.Quotient.mk (localizedIdeal I M)
    (algebraMap R (Localization M) r))) = _
  rw [forward_generator, backward_generator]
  rfl

theorem forward_backward : (forward I M).comp (backward I M) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (quotientMonoid I M)
  apply Ideal.Quotient.ringHom_ext
  ext r
  change forward I M (backward I M
    (algebraMap (R ⧸ I) (LocalizedQuotient I M) (Ideal.Quotient.mk I r))) = _
  rw [backward_generator, forward_generator]
  rfl

noncomputable def quotientLocalizationEquiv : QuotientLocalized I M ≃+* LocalizedQuotient I M :=
  RingEquiv.ofRingHom (forward I M) (backward I M) (forward_backward I M) (backward_forward I M)

#print axioms localizedIdeal
#print axioms quotientMonoid
#print axioms LocalizedQuotient
#print axioms QuotientLocalized
#print axioms baseToLocalizedQuotient
#print axioms baseToLocalizedQuotient_units
#print axioms localizationMap
#print axioms localizationMap_kills
#print axioms forward
#print axioms baseToQuotientLocalized
#print axioms baseToQuotientLocalized_kills
#print axioms quotientMap
#print axioms quotientMap_units
#print axioms backward
#print axioms forward_generator
#print axioms backward_generator
#print axioms backward_forward
#print axioms forward_backward
#print axioms quotientLocalizationEquiv
end Verification.LocalizationQuotient
