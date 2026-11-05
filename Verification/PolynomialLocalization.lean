/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizationQuotient
import Verification.PolynomialQuotient
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Polynomial Localization

The open-locus part of the original exchange strata. Localizing the
globally presented polynomial quotient is identified with the same
exchange equations over the localized coefficient ring.
-/
namespace Verification.PolynomialLocalization
open MvPolynomial
variable {R α : Type*} [CommRing R] (M : Submonoid R)
attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable abbrev coefficientMonoid : Submonoid (MvPolynomial α R) := M.map C
abbrev LocalPolynomial := Localization (coefficientMonoid (α := α) M)

noncomputable def polynomialLocalizationEquiv :
    LocalPolynomial (α := α) M ≃ₐ[MvPolynomial α R] MvPolynomial α (Localization M) :=
  IsLocalization.algEquiv (coefficientMonoid M) _ _

theorem polynomialLocalizationEquiv_generator (p : MvPolynomial α R) :
    polynomialLocalizationEquiv M (algebraMap (MvPolynomial α R) (LocalPolynomial M) p) =
      MvPolynomial.map (algebraMap R (Localization M)) p :=
  (polynomialLocalizationEquiv M).commutes p

theorem transport_ideal (J : Ideal (MvPolynomial α R)) :
    (J.map (algebraMap (MvPolynomial α R) (LocalPolynomial M))).map
      (polynomialLocalizationEquiv M).toRingHom =
        J.map (MvPolynomial.map (algebraMap R (Localization M))) := by
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  exact polynomialLocalizationEquiv_generator M p

/-- Localize the ring defined by the original polynomial equations. -/
noncomputable def openLocusEquiv (J : Ideal (MvPolynomial α R)) :
    Localization ((coefficientMonoid M).map (Ideal.Quotient.mk J)) ≃+*
      (MvPolynomial α (Localization M) ⧸
        J.map (MvPolynomial.map (algebraMap R (Localization M)))) :=
  (Verification.LocalizationQuotient.quotientLocalizationEquiv J (coefficientMonoid M)).symm.trans
    (Ideal.quotientEquiv _ _ (polynomialLocalizationEquiv M).toRingEquiv
      (transport_ideal M J).symm)

open Verification.StratumPresentation
variable {ι κ : Type*}

/-- The open localization of the original exchange presentation, with its
exchange equations mapped to the localized coefficient ring. -/
noncomputable def exchangeOpenLocusEquiv (x g : (ι ⊕ κ) → R) :
    Localization ((coefficientMonoid M).map (Ideal.Quotient.mk (exchangeIdeal x g))) ≃+*
      (MvPolynomial (ι ⊕ κ) (Localization M) ⧸
        exchangeIdeal (fun v => algebraMap R (Localization M) (x v))
          (fun v => algebraMap R (Localization M) (g v))) :=
  (openLocusEquiv M (exchangeIdeal x g)).trans
    (Ideal.quotEquivOfEq (Verification.PolynomialQuotient.map_exchangeIdeal
      (algebraMap R (Localization M)) x g))

#print axioms coefficientMonoid
#print axioms LocalPolynomial
#print axioms polynomialLocalizationEquiv
#print axioms polynomialLocalizationEquiv_generator
#print axioms transport_ideal
#print axioms openLocusEquiv
#print axioms exchangeOpenLocusEquiv
end Verification.PolynomialLocalization
