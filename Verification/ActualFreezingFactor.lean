/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualDivisorPresentation
import Verification.FreezingIndex
import Verification.PartnerRelabel
import Verification.FreezingPresentation

/-!
# Actual Freezing Factor

The actual divisor in the fixed global exchange ring has an affine
free-partner factor. The residual ring is still given with its literal
coefficient constraint at v and the exchange equations on nonneighbors;
the primitive torus-coordinate simplification is a further step.
-/
noncomputable section
namespace Verification.ActualFreezingFactor
open MvPolynomial Verification.FrozenAcyclicCover Verification.ActualFreezingDivisor
open Verification.ActualDivisorPresentation Verification.LocallyClosedPresentation
open Verification.FreezingIndex
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)

def Base := LocalBase (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)

instance baseCommRing : CommRing (Base R κ n B v) :=
  inferInstanceAs (CommRing (LocalBase (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)))

def original (i : (PUnit.{1} ⊕ Remaining κ n B v) ⊕ Neighbor κ n B v) : Base R κ n B v :=
  baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
    (initialFamily R κ n ((partners κ n B v).symm i))

def exchange (i : (PUnit.{1} ⊕ Remaining κ n B v) ⊕ Neighbor κ n B v) : Base R κ n B v :=
  baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
    (exchangeFamily R κ n B ((partners κ n B v).symm i))

omit [Fintype κ] in
theorem original_zero (u : PUnit.{1}) : original R κ n B v (Sum.inl (Sum.inl u)) = 0 := by
  cases u
  change algebraMap (ActualStratum.OriginalPolynomial R (Fin n) κ ⧸ coefficientZeroIdeal R κ n v)
    (LocalBase (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v))
      (Ideal.Quotient.mk (coefficientZeroIdeal R κ n v) (X (Sum.inl v))) = 0
  have hz : Ideal.Quotient.mk (coefficientZeroIdeal R κ n v) (X (Sum.inl v)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hz, map_zero]

omit [Fintype κ] in
theorem neighbor_isUnit (i : Neighbor κ n B v) : IsUnit (original R κ n B v (Sum.inr i)) := by
  change IsUnit (algebraMap _ (LocalBase (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v))
    (Ideal.Quotient.mk (coefficientZeroIdeal R κ n v) (X (Sum.inl i.1))))
  apply IsLocalization.map_units _
    (⟨Ideal.Quotient.mk (coefficientZeroIdeal R κ n v) (X (Sum.inl i.1)), ?_⟩ :
      coefficientOpenMonoid (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v))
  apply Submonoid.subset_closure
  exact ⟨Sum.inl i, rfl⟩

def neighborUnits (i : Neighbor κ n B v) : (Base R κ n B v)ˣ := (neighbor_isUnit R κ n B v i).unit

def residualIdeal : Ideal (MvPolynomial (Remaining κ n B v) (Base R κ n B v)) :=
  FreezingPresentation.remainingIdeal (original R κ n B v) (exchange R κ n B v)

def Residual := MvPolynomial (Remaining κ n B v) (Base R κ n B v) ⧸ residualIdeal R κ n B v

instance residualCommRing : CommRing (Residual R κ n B v) :=
  inferInstanceAs (CommRing (MvPolynomial (Remaining κ n B v) (Base R κ n B v) ⧸ residualIdeal R κ n B v))

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)

def affineFactorEquiv : Divisor R κ n B v ≃+* Polynomial (Residual R κ n B v) :=
  (divisorPresentationEquiv R κ n B v hpos hneg hsupport).trans
    ((PartnerRelabel.quotientEquiv (partners κ n B v)
      (fun i => baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
        (initialFamily R κ n i))
      (fun i => baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
        (exchangeFamily R κ n B i))).toRingEquiv.trans
      ((FreezingPresentation.preparedEquiv (original R κ n B v) (exchange R κ n B v)
        (neighborUnits R κ n B v) (original_zero R κ n B v)
        (fun i => (neighbor_isUnit R κ n B v i).unit_spec.symm)).toRingEquiv.trans
          (pUnitAlgEquiv (Residual R κ n B v)).toRingEquiv))

#print axioms Base
#print axioms baseCommRing
#print axioms original
#print axioms exchange
#print axioms original_zero
#print axioms neighbor_isUnit
#print axioms neighborUnits
#print axioms residualIdeal
#print axioms Residual
#print axioms residualCommRing
#print axioms affineFactorEquiv
end Verification.ActualFreezingFactor
