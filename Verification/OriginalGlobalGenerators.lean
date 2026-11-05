/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenGlobalSmooth

/-!
# Original Global Generators

The universal property of the literal global exchange ring, retaining
its actual scalar, original and mutated generators. Frozen units and the
ordinary exchange equations are the only data needed to construct a map.
-/
noncomputable section
namespace Verification.OriginalGlobalGenerators
open MvPolynomial
open scoped BigOperators
open Verification.FrozenAcyclicCover Verification.ActualStratum Verification.StratumPresentation
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable {S : Type} [CommRing S] (f : R →+* S) (x : Fin n ⊕ κ → S) (y : Fin n → S)

def polynomialMap : MvPolynomial (Fin n ⊕ Empty) (OriginalPolynomial R (Fin n) κ) →+* S :=
  eval₂Hom (eval₂Hom f x) (Sum.elim y Empty.elim)

variable (hxy : ∀ i : Fin n, x (Sum.inl i) * y i =
  (∏ a, x a ^ (B a (Sum.inl i)).toNat) + ∏ a, x a ^ (-B a (Sum.inl i)).toNat)

def presentationMap : PolynomialPresentation R κ n B →+* S :=
  Ideal.Quotient.lift _ (polynomialMap R κ n f x y) (by
    have hker : exchangeIdeal (initialPolynomial R (Fin n) κ Empty (noMutable κ))
        (exchangePolynomial R (Fin n) κ Empty B) ≤ RingHom.ker (polynomialMap R κ n f x y) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      cases i with
      | inl i =>
        change polynomialMap R κ n f x y (exchangeRelation _ _ (Sum.inl i)) = 0
        simp [polynomialMap, exchangeRelation, initialPolynomial, exchangePolynomial, hxy i]
      | inr e => exact e.elim
    exact fun a ha => hker ha)

variable (hx : ∀ k : κ, IsUnit (x (Sum.inr k)))

def lift : Global R κ n B →+* S :=
  IsLocalization.lift (S := Global R κ n B)
    (M := FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B)
    (g := presentationMap R κ n B f x y hxy)
    (SplitExchangeChart.units_on_closure _ _ (by
      intro k
      simpa [presentationMap, FrozenOpenChart.original, polynomialMap] using hx k.val))

theorem lift_scalar (a : R) :
    lift R κ n B f x y hxy hx (algebraMap R (Global R κ n B) a) = f a := by
  change IsLocalization.lift _ (algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)
    (Ideal.Quotient.mk _ (C (C a)))) = _
  rw [IsLocalization.lift_eq]
  simp [presentationMap, polynomialMap]

theorem lift_initial (a : Fin n ⊕ κ) :
    lift R κ n B f x y hxy hx (initial R κ n B a) = x a := by
  change IsLocalization.lift _ (algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)
    (Ideal.Quotient.mk _ (C (X a)))) = _
  rw [IsLocalization.lift_eq]
  simp [presentationMap, polynomialMap]

theorem lift_mutated (i : Fin n) :
    lift R κ n B f x y hxy hx (mutated R κ n B i) = y i := by
  change IsLocalization.lift _ (algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)
    (Ideal.Quotient.mk _ (X (Sum.inl i)))) = _
  rw [IsLocalization.lift_eq]
  simp [presentationMap, polynomialMap]

theorem hom_ext (g h : Global R κ n B →+* S)
    (hscalar : ∀ a : R, g (algebraMap R (Global R κ n B) a) = h (algebraMap R (Global R κ n B) a))
    (hinitial : ∀ a, g (initial R κ n B a) = h (initial R κ n B a))
    (hmutated : ∀ i, g (mutated R κ n B i) = h (mutated R κ n B i)) : g = h := by
  apply IsLocalization.ringHom_ext (M := FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B)
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext'
  · apply MvPolynomial.ringHom_ext
    · exact hscalar
    · exact hinitial
  · intro i
    cases i with
    | inl i => exact hmutated i
    | inr e => exact e.elim

#print axioms polynomialMap
#print axioms presentationMap
#print axioms lift
#print axioms lift_scalar
#print axioms lift_initial
#print axioms lift_mutated
#print axioms hom_ext
end Verification.OriginalGlobalGenerators
