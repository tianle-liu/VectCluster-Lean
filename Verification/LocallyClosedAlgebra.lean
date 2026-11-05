/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocallyClosedPresentation

/-!
# Locally Closed Algebra

The closed/open presentation equivalence respects the base algebra.
These generator identities upgrade the ring equivalences used for original
strata to algebra equivalences, as required for smoothness over the base.
-/
namespace Verification.LocallyClosedAlgebra
open MvPolynomial Verification.PolynomialLocalization
open Verification.StratumPresentation Verification.LocallyClosedPresentation
variable {R α ι κ β : Type*} [CommRing R]
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem openLocusEquiv_generator (M : Submonoid R) (J : Ideal (MvPolynomial α R))
    (p : MvPolynomial α R) :
    openLocusEquiv M J
      (algebraMap (MvPolynomial α R ⧸ J) _ (Ideal.Quotient.mk J p)) =
      Ideal.Quotient.mk (J.map (MvPolynomial.map (algebraMap R (Localization M))))
        (MvPolynomial.map (algebraMap R (Localization M)) p) := by
  rw [openLocusEquiv, RingEquiv.trans_apply]
  change (Ideal.quotientEquiv _ _ (polynomialLocalizationEquiv (α := α) M).toRingEquiv
    (transport_ideal M J).symm)
      (Verification.LocalizationQuotient.backward J (coefficientMonoid (α := α) M)
        (algebraMap (MvPolynomial α R ⧸ J) _ (Ideal.Quotient.mk J p))) = _
  rw [Verification.LocalizationQuotient.backward_generator]
  change Ideal.Quotient.mk _
    (polynomialLocalizationEquiv (α := α) M
      (algebraMap (MvPolynomial α R) (LocalPolynomial (α := α) M) p)) = _
  rw [polynomialLocalizationEquiv_generator]

theorem exchangeOpenLocusEquiv_generator (M : Submonoid R) (x g : (ι ⊕ κ) → R)
    (p : MvPolynomial (ι ⊕ κ) R) :
    exchangeOpenLocusEquiv M x g
      (algebraMap (MvPolynomial (ι ⊕ κ) R ⧸ exchangeIdeal x g) _
        (Ideal.Quotient.mk (exchangeIdeal x g) p)) =
      Ideal.Quotient.mk (exchangeIdeal (fun v => algebraMap R (Localization M) (x v))
        (fun v => algebraMap R (Localization M) (g v)))
        (MvPolynomial.map (algebraMap R (Localization M)) p) := by
  dsimp only [exchangeOpenLocusEquiv, RingEquiv.trans_apply]
  rw [openLocusEquiv_generator M (exchangeIdeal x g) p]
  rfl

theorem localizeClosedEquiv_coefficient (I : Ideal R) (x g : (ι ⊕ κ) → R) (v : β → R)
    (r : R) :
    localizeClosedEquiv I x g v
      (algebraMap (ClosedRing I x g) _ (closedCoefficient I x g r)) =
      algebraMap (ChangedClosedRing I x g) (Localization (changedOpenMonoid I x g v))
        (Ideal.Quotient.mk _ (C (Ideal.Quotient.mk I r))) := by
  rw [localizeClosedEquiv, IsLocalization.ringEquivOfRingEquiv_eq, closedEquiv_coefficient]

theorem locallyClosedEquiv_coefficient (I : Ideal R) (x g : (ι ⊕ κ) → R) (v : β → R)
    (r : R) :
    locallyClosedEquiv I x g v
      (algebraMap (ClosedRing I x g) _ (closedCoefficient I x g r)) =
      Ideal.Quotient.mk (exchangeIdeal (fun a => baseMap I v (x a))
        (fun a => baseMap I v (g a))) (C (baseMap I v r)) := by
  dsimp only [locallyClosedEquiv, RingEquiv.trans_apply]
  rw [localizeClosedEquiv_coefficient I x g v r]
  simpa only [map_C] using exchangeOpenLocusEquiv_generator (coefficientOpenMonoid I v)
    (fun a => Ideal.Quotient.mk I (x a)) (fun a => Ideal.Quotient.mk I (g a))
    (C (Ideal.Quotient.mk I r))

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable def locallyClosedEquivAlg (I : Ideal R) (x g : (ι ⊕ κ) → R) (v : β → R) :
    LocallyClosedRing I x g v ≃ₐ[R]
      (MvPolynomial (ι ⊕ κ) (LocalBase I v) ⧸
        exchangeIdeal (fun a => baseMap I v (x a)) (fun a => baseMap I v (g a))) :=
  AlgEquiv.ofRingEquiv (f := locallyClosedEquiv I x g v) (fun r => by
    exact locallyClosedEquiv_coefficient I x g v r)

#print axioms openLocusEquiv_generator
#print axioms exchangeOpenLocusEquiv_generator
#print axioms localizeClosedEquiv_coefficient
#print axioms locallyClosedEquiv_coefficient
#print axioms locallyClosedEquivAlg
end Verification.LocallyClosedAlgebra
