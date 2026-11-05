/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EliminationWithConstraints
import Mathlib.RingTheory.Localization.Basic

/-!
# Stratum Presentation

The exchange-presentation calculation for zero strata, manuscript.tex:375–377.
The original coordinates vanish on the selected indices and are invertible
on the complementary indices. The exchange ideal is literally the simultaneous
constraint/elimination ideal, hence its quotient is the polynomial algebra on
the free exchange partners over the residual coefficient quotient.

The second section constructs an actual base by killing the selected original
variables in a polynomial algebra and localizing the complementary variables.
Its zero/unit properties are proved, not additional assumptions. Identifying
the residual exchange polynomials with particular torus characters, and the
cited identification of the exchange presentation with a cluster algebra, are
separate statements.
-/

noncomputable section

namespace Verification.StratumPresentation

open MvPolynomial

variable {R ι κ : Type*} [CommRing R]

def exchangeRelation (x f : (ι ⊕ κ) → R) (v : ι ⊕ κ) :
    MvPolynomial (ι ⊕ κ) R := C (x v) * X v - C (f v)

def exchangeIdeal (x f : (ι ⊕ κ) → R) : Ideal (MvPolynomial (ι ⊕ κ) R) :=
  Ideal.span (Set.range (exchangeRelation x f))

/-- The residual equations on the base arise exactly at the vanishing indices. -/
def coefficientIdeal (f : (ι ⊕ κ) → R) : Ideal R :=
  Ideal.span (Set.range (fun i => f (Sum.inl i)))

theorem coefficientIdeal_le_comap (x f : (ι ⊕ κ) → R)
    (hzero : ∀ i, x (Sum.inl i) = 0) :
    coefficientIdeal f ≤ (exchangeIdeal x f).comap C := by
  apply Ideal.span_le.mpr
  rintro r ⟨i, rfl⟩
  change C (f (Sum.inl i)) ∈ exchangeIdeal x f
  have hm : exchangeRelation x f (Sum.inl i) ∈ exchangeIdeal x f :=
    Ideal.subset_span (Set.mem_range_self (Sum.inl i))
  have hn : -C (f (Sum.inl i)) ∈ exchangeIdeal x f := by
    simpa only [exchangeRelation, hzero, map_zero, zero_mul, zero_sub] using hm
  simpa only [neg_neg] using (exchangeIdeal x f).neg_mem hn

/-- Equality of the actual defining ideals, before taking any quotient. -/
theorem exchangeIdeal_eq_constraints (x f : (ι ⊕ κ) → R) (a : κ → Rˣ)
    (hzero : ∀ i, x (Sum.inl i) = 0)
    (hunit : ∀ k, x (Sum.inr k) = (a k : R)) :
    exchangeIdeal x f = EliminationWithConstraints.constraints
      (coefficientIdeal f) a (fun k => f (Sum.inr k)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨v, rfl⟩
    cases v with
    | inl i =>
      simp only [exchangeRelation, hzero, map_zero, zero_mul, zero_sub]
      apply (EliminationWithConstraints.constraints
        (coefficientIdeal f) a (fun k => f (Sum.inr k))).neg_mem
      exact Ideal.subset_span (Or.inl
        ⟨f (Sum.inl i), Ideal.subset_span (Set.mem_range_self i), rfl⟩)
    | inr k =>
      have hm : Elimination.relation a (fun k => f (Sum.inr k)) k ∈
          EliminationWithConstraints.constraints (ι := ι)
            (coefficientIdeal f) a (fun k => f (Sum.inr k)) :=
        Ideal.subset_span (Or.inr (Set.mem_range_self k))
      simpa only [Elimination.relation, exchangeRelation, hunit] using hm
  · apply Ideal.span_le.mpr
    rintro p (⟨r, hr, rfl⟩ | ⟨k, rfl⟩)
    · exact coefficientIdeal_le_comap x f hzero hr
    · have hm : exchangeRelation x f (Sum.inr k) ∈ exchangeIdeal x f :=
        Ideal.subset_span (Set.mem_range_self (Sum.inr k))
      simpa only [Elimination.relation, exchangeRelation, hunit] using hm

/-- The free exchange partners are affine coordinates over the exact residual
coefficient quotient. -/
def quotientEquiv (x f : (ι ⊕ κ) → R) (a : κ → Rˣ)
    (hzero : ∀ i, x (Sum.inl i) = 0)
    (hunit : ∀ k, x (Sum.inr k) = (a k : R)) :
    (MvPolynomial (ι ⊕ κ) R ⧸ exchangeIdeal x f) ≃ₐ[R]
      MvPolynomial ι (R ⧸ coefficientIdeal f) :=
  (Ideal.quotientEquivAlgOfEq R (exchangeIdeal_eq_constraints x f a hzero hunit)).trans
    (EliminationWithConstraints.quotientEquiv (coefficientIdeal f) a
      (fun k => f (Sum.inr k)))

universe u

def quotientSpecIso {S α β : Type u} [CommRing S]
    (x f : (α ⊕ β) → S) (a : β → Sˣ)
    (hzero : ∀ i, x (Sum.inl i) = 0)
    (hunit : ∀ k, x (Sum.inr k) = (a k : S)) :
    AlgebraicGeometry.Spec (CommRingCat.of
      (MvPolynomial (α ⊕ β) S ⧸ exchangeIdeal x f)) ≅
      AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial α (S ⧸ coefficientIdeal f))) :=
  AlgebraicGeometry.Scheme.Spec.mapIso
    (quotientEquiv x f a hzero hunit).toRingEquiv.toCommRingCatIso.symm.op

section LocalizedOriginals

variable (R ι κ)

def zeroCoordinateIdeal : Ideal (MvPolynomial (ι ⊕ κ) R) :=
  Ideal.span (Set.range (fun i : ι => (X (Sum.inl i) : MvPolynomial (ι ⊕ κ) R)))

abbrev OriginalQuotient := MvPolynomial (ι ⊕ κ) R ⧸ zeroCoordinateIdeal R ι κ

def nonzeroCoordinateMonoid : Submonoid (OriginalQuotient R ι κ) :=
  Submonoid.closure (Set.range (fun k : κ =>
    Ideal.Quotient.mk (zeroCoordinateIdeal R ι κ) (X (Sum.inr k))))

/-- The locally closed coordinate stratum in the original polynomial space. -/
abbrev OriginalStratum := Localization (nonzeroCoordinateMonoid R ι κ)

def originalCoordinate (v : ι ⊕ κ) : OriginalStratum R ι κ :=
  algebraMap (OriginalQuotient R ι κ) (OriginalStratum R ι κ)
    (Ideal.Quotient.mk (zeroCoordinateIdeal R ι κ) (X v))

theorem originalCoordinate_zero (i : ι) :
    originalCoordinate R ι κ (Sum.inl i) = 0 := by
  have h : Ideal.Quotient.mk (zeroCoordinateIdeal R ι κ) (X (Sum.inl i)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  simp only [originalCoordinate, h, map_zero]

theorem originalCoordinate_unit (k : κ) :
    IsUnit (originalCoordinate R ι κ (Sum.inr k)) := by
  apply IsLocalization.map_units (M := nonzeroCoordinateMonoid R ι κ)
    (OriginalStratum R ι κ)
    ⟨Ideal.Quotient.mk (zeroCoordinateIdeal R ι κ) (X (Sum.inr k)), ?_⟩
  exact Submonoid.subset_closure (Set.mem_range_self k)

def coordinateUnit (k : κ) : (OriginalStratum R ι κ)ˣ :=
  (originalCoordinate_unit R ι κ k).unit

theorem coordinateUnit_val (k : κ) :
    (coordinateUnit R ι κ k : OriginalStratum R ι κ) =
      originalCoordinate R ι κ (Sum.inr k) :=
  (originalCoordinate_unit R ι κ k).unit_spec

/-- Applying the actual presentation calculation to the actual localized base
requires no assumed zero/unit properties of the original coordinates. -/
def localizedQuotientEquiv (f : (ι ⊕ κ) → OriginalStratum R ι κ) :
    (MvPolynomial (ι ⊕ κ) (OriginalStratum R ι κ) ⧸
      exchangeIdeal (originalCoordinate R ι κ) f) ≃ₐ[OriginalStratum R ι κ]
        MvPolynomial ι (OriginalStratum R ι κ ⧸ coefficientIdeal f) :=
  quotientEquiv (originalCoordinate R ι κ) f (coordinateUnit R ι κ)
    (originalCoordinate_zero R ι κ) (fun k => (coordinateUnit_val R ι κ k).symm)

end LocalizedOriginals

#print axioms exchangeRelation
#print axioms exchangeIdeal
#print axioms coefficientIdeal
#print axioms coefficientIdeal_le_comap
#print axioms exchangeIdeal_eq_constraints
#print axioms quotientEquiv
#print axioms quotientSpecIso
#print axioms zeroCoordinateIdeal
#print axioms OriginalQuotient
#print axioms nonzeroCoordinateMonoid
#print axioms OriginalStratum
#print axioms originalCoordinate
#print axioms originalCoordinate_zero
#print axioms originalCoordinate_unit
#print axioms coordinateUnit
#print axioms coordinateUnit_val
#print axioms localizedQuotientEquiv

end Verification.StratumPresentation
