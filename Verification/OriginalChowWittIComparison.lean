/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ChowWittFiberProductInput
import Verification.OriginalASChowVanishing

/-!
# Original Chow Witt I Comparison

The first arrow of the manuscript's positive Chow--Witt comparison.
On the actual AS exchange scheme, positive Chow vanishing collapses the
ordinary Milnor--Witt fiber square. The isomorphism below is the given
coefficient morphism CW^p → Nis H^p(I^p), not an unnormalized equivalence.
The second arrow to Witt cohomology is not asserted here.
-/
noncomputable section
namespace Verification.OriginalChowWittIComparison
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry
open Verification.IndependentChartIndex Verification.FrozenAcyclicCover
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hall : ∀ I, ExchangeOpenCover.Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun a i => B a (Sum.inl i)) I)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (RS : RostSupportInput.Theory T) (P : RostPrincipalLocalizationInput.Theory T)
variable (Z : RostWeightZero.IntegralConvention T)
variable (E : RostCanonicalCoefficients.GenericZeroEvaluation T F Z)
variable (U : OriginalRostUnitTerms.UnitsConvention T)
variable (UN : RostCanonicalCoefficients.UnitsNaturality T F U)
variable (N : RostPrincipalResidueInput.Normalization T P F Z E U)
variable (C : OriginalRostBoundaryCharts.Standard R κ n B hpos hneg hsupport
  (OriginalASChowVanishing.selected_injective κ n B hall)
  (OriginalASChowVanishing.tame R κ n B hall) T RS P)
variable (CH : Scheme → ℕ → AddCommGrp)
variable (K : RostMilnorInput.ChowComparison T CH) (Neg : RostMilnorInput.NegativeWeights T)
variable {A : Type*}
variable (NT : StrictNisnevichInput.Theory A) (IP : ℕ → A) (CW : Scheme → ℕ → AddCommGrp)
variable (Q : ChowWittFiberProductInput.Theory NT R IP CW CH)
variable (HW : ChowWittFiberProductInput.Standard NT R IP CW CH Q)

def smooth : Algebra.Smooth R (Global R κ n B) :=
  GlobalExchangeSmooth.global_smooth_tame R κ n B hpos hneg hsupport
    (OriginalASChowVanishing.selected_injective κ n B hall)
    (OriginalASChowVanishing.tame R κ n B hall)

def comparison (p : ℕ) : CW (Spec (CommRingCat.of (Global R κ n B))) p →+
    NT.cohomology (Spec (CommRingCat.of (Global R κ n B))) (IP p) p := by
  letI := smooth R κ n B hall hpos hneg hsupport
  exact Q.comparison (Global R κ n B) p

include C UN N K Neg in
theorem positive_chow (p : ℕ) (hp : 0 < p) :
    Subsingleton (CH (Spec (CommRingCat.of (Global R κ n B))) p) := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact OriginalASChowVanishing.positive_subsingleton R κ n B hall hpos hneg hsupport
    T F RS P Z E U UN N C CH K Neg q

include C UN N K Neg HW in
theorem comparison_bijective (p : ℕ) (hp : 0 < p) : Function.Bijective
    (comparison R κ n B hall hpos hneg hsupport CH NT IP CW Q p) := by
  letI := smooth R κ n B hall hpos hneg hsupport
  letI := positive_chow R κ n B hall hpos hneg hsupport
    T F RS P Z E U UN N C CH K Neg p hp
  exact ChowWittFiberProductInput.comparison_bijective NT R IP CW CH Q (Global R κ n B) p HW

def comparisonEquiv (p : ℕ) (hp : 0 < p) :
    CW (Spec (CommRingCat.of (Global R κ n B))) p ≃+
      NT.cohomology (Spec (CommRingCat.of (Global R κ n B))) (IP p) p :=
  AddEquiv.ofBijective (comparison R κ n B hall hpos hneg hsupport CH NT IP CW Q p)
    (comparison_bijective R κ n B hall hpos hneg hsupport T F RS P Z E U UN N C
      CH K Neg NT IP CW Q HW p hp)

theorem comparisonEquiv_apply (p : ℕ) (hp : 0 < p)
    (x : CW (Spec (CommRingCat.of (Global R κ n B))) p) :
    comparisonEquiv R κ n B hall hpos hneg hsupport T F RS P Z E U UN N C
      CH K Neg NT IP CW Q HW p hp x =
      comparison R κ n B hall hpos hneg hsupport CH NT IP CW Q p x := rfl

#print axioms smooth
#print axioms comparison
#print axioms positive_chow
#print axioms comparison_bijective
#print axioms comparisonEquiv
#print axioms comparisonEquiv_apply
end Verification.OriginalChowWittIComparison
