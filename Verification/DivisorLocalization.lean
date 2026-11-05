/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizationQuotient

/-!
# Divisor Localization

Extra coordinates already invertible on a closed locus can be included
in its localization monoid. The equivalence uses the literal quotient and
localization maps and preserves the original coefficient ring.
-/
noncomputable section
namespace Verification.DivisorLocalization
open Verification.LocalizationQuotient
variable {A : Type*} [CommRing A] (I : Ideal A) (M N : Submonoid A) (hMN : M ≤ N)
variable (hN : ∀ a ∈ N, IsUnit (baseToQuotientLocalized I M a))

def toLargerLocalization : Localization M →+* LocalizedQuotient I N :=
  IsLocalization.lift (g := baseToLocalizedQuotient I N) (fun m : M =>
    IsLocalization.map_units (LocalizedQuotient I N)
      (⟨Ideal.Quotient.mk I m, Submonoid.mem_map_of_mem _ (hMN m.2)⟩ : quotientMonoid I N))

theorem toLargerLocalization_generator (a : A) :
    toLargerLocalization I M N hMN (algebraMap A (Localization M) a) =
      algebraMap (A ⧸ I) (LocalizedQuotient I N) (Ideal.Quotient.mk I a) := by
  rw [toLargerLocalization, IsLocalization.lift_eq]
  rfl

def forward : QuotientLocalized I M →+* LocalizedQuotient I N :=
  Ideal.Quotient.lift (localizedIdeal I M) (toLargerLocalization I M N hMN) (by
    change localizedIdeal I M ≤ RingHom.ker (toLargerLocalization I M N hMN)
    rw [localizedIdeal, Ideal.map_le_iff_le_comap]
    intro a ha
    change toLargerLocalization I M N hMN (algebraMap A (Localization M) a) = 0
    rw [toLargerLocalization_generator, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero])

def backward : LocalizedQuotient I N →+* QuotientLocalized I M :=
  IsLocalization.lift (M := quotientMonoid I N) (g := quotientMap I M) (by
    rintro ⟨_, a, ha, rfl⟩
    exact hN a ha)

theorem forward_generator (a : A) :
    forward I M N hMN (Ideal.Quotient.mk (localizedIdeal I M)
      (algebraMap A (Localization M) a)) =
    algebraMap (A ⧸ I) (LocalizedQuotient I N) (Ideal.Quotient.mk I a) :=
  toLargerLocalization_generator I M N hMN a

theorem backward_generator (a : A) :
    backward I M N hN (algebraMap (A ⧸ I) (LocalizedQuotient I N) (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk (localizedIdeal I M) (algebraMap A (Localization M) a) := by
  rw [backward, IsLocalization.lift_eq]
  rfl

theorem backward_forward : (backward I M N hN).comp (forward I M N hMN) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext M
  ext a
  change backward I M N hN (forward I M N hMN
    (Ideal.Quotient.mk (localizedIdeal I M) (algebraMap A (Localization M) a))) = _
  rw [forward_generator, backward_generator]
  rfl

theorem forward_backward : (forward I M N hMN).comp (backward I M N hN) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (quotientMonoid I N)
  apply Ideal.Quotient.ringHom_ext
  ext a
  change forward I M N hMN (backward I M N hN
    (algebraMap (A ⧸ I) (LocalizedQuotient I N) (Ideal.Quotient.mk I a))) = _
  rw [backward_generator, forward_generator]
  rfl

def equiv : QuotientLocalized I M ≃ₐ[A] LocalizedQuotient I N :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofRingHom (forward I M N hMN) (backward I M N hN)
      (forward_backward I M N hMN hN) (backward_forward I M N hMN hN))
    (fun a => forward_generator I M N hMN a)

#print axioms toLargerLocalization
#print axioms toLargerLocalization_generator
#print axioms forward
#print axioms backward
#print axioms forward_generator
#print axioms backward_generator
#print axioms backward_forward
#print axioms forward_backward
#print axioms equiv
end Verification.DivisorLocalization
