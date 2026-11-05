/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ResidualReindexConditions

/-!
# Scalar Freezing Iteration

Closure under another freezing for the actual scalar exchange seed
class used in the AS framed-freezing lemma. Both scalar terms are allowed
at the input; the output is again an actual global scalar presentation,
with fewer mutable vertices, the inherited acyclic order, and AS for every
independent set. This theorem does not assert Picard vanishing.
-/
noncomputable section
namespace Verification.ScalarFreezingIteration
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.ActualScalarFreezing Verification.FreezingIndex
open Verification.ResidualScalarReentry Verification.IteratedScalarNormalized
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
attribute [local instance] Verification.ActualFreezingConstraint.remainingFintype
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ) (v : Fin n)

theorem closed_scalar_seed
    (hpos : ∀ s i : Fin n, ¬ s < i → (B (Sum.inl s) (Sum.inl i)).toNat = 0)
    (hneg : ∀ s i : Fin n, ¬ i < s → (-B (Sum.inl s) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
    (hall : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
      AnticliqueSubcolumns.AS (fun q j => B q (Sum.inl j)) I) :
    ∃ (m r : ℕ) (B' : (Fin m ⊕ Fin r) → (Fin m ⊕ Empty) → ℤ) (c : Fin m → Rˣ),
      m < n ∧
      Nonempty (ScalarDivisorPresentation.Divisor R κ n B a b v ≃ₐ[R]
        Polynomial (ScalarFrozenGlobal.Global R (Fin r) m B' c (fun _ => 1))) ∧
      (∃ g : Fin m ↪ Fin n,
        (∀ w, w ∈ Set.range g ↔ w ≠ v ∧ ¬ ExchangeRing.Adjacent (laterWeights κ n B) v w) ∧
        ∀ s i, B' (Sum.inl s) (Sum.inl i) = B (Sum.inl (g s)) (Sum.inl (g i))) ∧
      (∀ s i : Fin m, ¬ s < i → (B' (Sum.inl s) (Sum.inl i)).toNat = 0) ∧
      (∀ s i : Fin m, ¬ i < s → (-B' (Sum.inl s) (Sum.inl i)).toNat = 0) ∧
      (∀ i j, earlierWeights (Fin r) m B' i j = 0 ↔ laterWeights (Fin r) m B' i j = 0) ∧
      (∀ I : Finset (Fin m), Independent (laterWeights (Fin r) m B') I →
        AnticliqueSubcolumns.AS (fun q j => B' q (Sum.inl j)) I) := by
  have hv : AnticliqueSubcolumns.AS (fun q j => B q (Sum.inl j)) ({v} : Finset (Fin n)) := by
    apply hall
    intro i hi j hj
    have hi' := Finset.mem_singleton.mp hi
    have hj' := Finset.mem_singleton.mp hj
    subst i
    subst j
    simp [ExchangeRing.Adjacent]
  letI : Module.Free ℤ (QuotientLattice κ n B v) :=
    NormalizedScalarFreezing.quotientLattice_free κ n B v hpos hneg hsupport hv
  obtain ⟨d,_,⟨E⟩⟩ := actual_normalized_freezing R κ n B a b v hpos hneg hsupport hv
  let h := (Fintype.orderIsoFinOfCardEq (Remaining κ n B v) rfl).symm
  let e := (Module.finBasis ℤ (QuotientLattice κ n B v)).repr
  refine ⟨_,_,reindexedMatrix κ n B v h.toEquiv e,
    reindexedCoefficient R κ n B a b v d h.toEquiv,
    remaining_card_lt κ n B v,
    ⟨E.trans (Polynomial.mapAlgEquiv (reentryEquiv R κ n B a b v d h.toEquiv e))⟩,?_,?_,?_,?_,?_⟩
  · refine ⟨⟨fun i => (h.symm i).val, Subtype.val_injective.comp h.symm.injective⟩,?_,fun _ _ => rfl⟩
    intro w
    constructor
    · rintro ⟨i,rfl⟩
      exact (h.symm i).property
    · intro hw
      exact ⟨h ⟨w,hw⟩,by simp⟩
  · exact ResidualReindexConditions.positive_order κ n B v h e hpos
  · exact ResidualReindexConditions.negative_order κ n B v h e hneg
  · exact ResidualReindexConditions.support κ n B v h e hsupport
  · exact ResidualReindexConditions.allAS κ n B v h e hpos hneg hsupport hall

#print axioms closed_scalar_seed
end Verification.ScalarFreezingIteration
