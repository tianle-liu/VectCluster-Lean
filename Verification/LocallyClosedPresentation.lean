/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PolynomialLocalization

/-!
# Locally Closed Presentation

The actual locally closed locus of a globally presented exchange ring.
We first impose a coefficient ideal inside the global quotient and then
localize specified original coefficients. Both operations are transported
to the coefficient ring, retaining the literal exchange equations.
-/
namespace Verification.LocallyClosedPresentation
open MvPolynomial Verification.StratumPresentation
variable {R ι κ β : Type*} [CommRing R]
variable (I : Ideal R) (x g : (ι ⊕ κ) → R) (v : β → R)

abbrev GlobalRing := MvPolynomial (ι ⊕ κ) R ⧸ exchangeIdeal x g
noncomputable abbrev closedIdeal : Ideal (GlobalRing x g) :=
  (Verification.PolynomialQuotient.coefficientIdeal I).map (Ideal.Quotient.mk (exchangeIdeal x g))
abbrev ClosedRing := GlobalRing x g ⧸ closedIdeal I x g

noncomputable def closedCoefficient (r : R) : ClosedRing I x g :=
  Ideal.Quotient.mk (closedIdeal I x g) (Ideal.Quotient.mk (exchangeIdeal x g) (C r))

noncomputable def openMonoid : Submonoid (ClosedRing I x g) :=
  Submonoid.closure (Set.range (fun b => closedCoefficient I x g (v b)))

abbrev LocallyClosedRing := Localization (openMonoid I x g v)

def coefficientOpenMonoid : Submonoid (R ⧸ I) :=
  Submonoid.closure (Set.range (fun b => Ideal.Quotient.mk I (v b)))

abbrev LocalBase := Localization (coefficientOpenMonoid I v)

def baseMap : R →+* LocalBase I v :=
  (algebraMap (R ⧸ I) _).comp (Ideal.Quotient.mk I)

abbrev ChangedClosedRing := MvPolynomial (ι ⊕ κ) (R ⧸ I) ⧸
  exchangeIdeal (fun a => Ideal.Quotient.mk I (x a)) (fun a => Ideal.Quotient.mk I (g a))

noncomputable def changedOpenMonoid : Submonoid (ChangedClosedRing I x g) :=
  ((coefficientOpenMonoid I v).map C).map (Ideal.Quotient.mk _)

noncomputable def closedEquiv : ClosedRing I x g ≃+* ChangedClosedRing I x g :=
  Verification.PolynomialQuotient.exchangeClosedLocusEquiv I x g

theorem closedEquiv_coefficient (r : R) :
    closedEquiv I x g (closedCoefficient I x g r) =
      Ideal.Quotient.mk _ (C (Ideal.Quotient.mk I r)) := by
  change Verification.PolynomialQuotient.exchangeClosedLocusEquiv I x g
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (C r))) = _
  rw [Verification.PolynomialQuotient.exchangeClosedLocusEquiv_generator, map_C]

theorem map_openMonoid :
    (openMonoid I x g v).map (closedEquiv I x g).toMonoidHom = changedOpenMonoid I x g v := by
  unfold openMonoid changedOpenMonoid coefficientOpenMonoid
  rw [MonoidHom.map_mclosure, MonoidHom.map_mclosure, MonoidHom.map_mclosure]
  apply congrArg Submonoid.closure
  rw [← Set.range_comp, ← Set.range_comp, ← Set.range_comp]
  apply congrArg Set.range
  funext b
  exact closedEquiv_coefficient I x g (v b)

noncomputable def localizeClosedEquiv : LocallyClosedRing I x g v ≃+*
    Localization (changedOpenMonoid I x g v) :=
  IsLocalization.ringEquivOfRingEquiv _ _ (closedEquiv I x g) (map_openMonoid I x g v)

/-- The globally presented ring, its actual closed locus, and its open
localization yield exactly the equations over the localized coefficient quotient. -/
noncomputable def locallyClosedEquiv : LocallyClosedRing I x g v ≃+*
    (MvPolynomial (ι ⊕ κ) (LocalBase I v) ⧸
      exchangeIdeal (fun a => baseMap I v (x a)) (fun a => baseMap I v (g a))) :=
  (localizeClosedEquiv I x g v).trans
    (Verification.PolynomialLocalization.exchangeOpenLocusEquiv (coefficientOpenMonoid I v)
      (fun a => Ideal.Quotient.mk I (x a)) (fun a => Ideal.Quotient.mk I (g a)))

#print axioms GlobalRing
#print axioms closedIdeal
#print axioms ClosedRing
#print axioms closedCoefficient
#print axioms openMonoid
#print axioms LocallyClosedRing
#print axioms coefficientOpenMonoid
#print axioms LocalBase
#print axioms baseMap
#print axioms ChangedClosedRing
#print axioms changedOpenMonoid
#print axioms closedEquiv
#print axioms closedEquiv_coefficient
#print axioms map_openMonoid
#print axioms localizeClosedEquiv
#print axioms locallyClosedEquiv
end Verification.LocallyClosedPresentation
