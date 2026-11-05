/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IteratedScalarNormalized

/-!
# Iterated AS Freezing

The algebraic closed-piece assertion in the AS framed-freezing lemma.
The actual whole divisor is an affine line over the normalized residual
scalar exchange quotient, whose frozen lattice is free and whose actual
selected columns satisfy AS. Picard vanishing and the scheme-theoretic
normal framing are not asserted by this theorem.
-/
noncomputable section
namespace Verification.IteratedASFreezing
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.ActualFreezingDivisor Verification.ActualFreezingCoefficient
open Verification.ActualScalarFreezing (FrozenLattice QuotientLattice)
open Verification.IteratedScalarNormalized
open Verification.NormalizedScalarFreezing (quotientLattice_free)
open Verification.ActualResidualColumns Verification.FreezingLattice
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
attribute [local instance] Verification.ActualFreezingConstraint.remainingFintype
attribute [local instance] Verification.ActualScalarFreezing.scalarPolynomialCommRing
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ) (v : Fin n)

theorem actual_AS_closed_freezing
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
    (hall : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
      AnticliqueSubcolumns.AS (fun a w => B a (Sum.inl w)) I) :
    ∃ d : Multiplicative (FrozenLattice κ n B v) →* Rˣ,
      d (Multiplicative.ofAdd (distinguishedColumn κ n B v)) = ScalarExchangeCharacters.prescribed (a v) (b v) ∧
      Nonempty (ScalarDivisorPresentation.Divisor R κ n B a b v ≃ₐ[R] Polynomial (NormalizedResidual R κ n B a b v d)) ∧
      Module.Free ℤ (QuotientLattice κ n B v) ∧
      ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
        (∀ i ∈ I, i ≠ v ∧ ¬ ExchangeRing.Adjacent (laterWeights κ n B) v i) →
        Function.Injective (residualMatrix κ n B v I) ∧
          Saturated (LinearMap.range (residualMatrix κ n B v I)) := by
  have hv : AnticliqueSubcolumns.AS (fun a w => B a (Sum.inl w)) ({v} : Finset (Fin n)) := by
    apply hall
    intro a ha b hb
    have ha' := Finset.mem_singleton.mp ha
    have hb' := Finset.mem_singleton.mp hb
    subst a
    subst b
    simp [ExchangeRing.Adjacent]
  obtain ⟨d,hd,he⟩ := actual_normalized_freezing R κ n B a b v hpos hneg hsupport hv
  refine ⟨d,hd,he,quotientLattice_free κ n B v hpos hneg hsupport hv,?_⟩
  intro I hI hn
  have hvI : v ∉ I := by intro h; exact (hn v h).1 rfl
  exact residual_AS_of_allAS κ n B v I hvI (fun i hi => (hn i hi).2)
    hpos hneg hsupport hall hI

#print axioms actual_AS_closed_freezing
end Verification.IteratedASFreezing
