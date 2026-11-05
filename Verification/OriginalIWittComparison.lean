/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalChowWittIComparison
import Verification.FundamentalIdealChowComparison

/-!
# Original I Witt Comparison

Both arrows in the manuscript's positive Chow--Witt comparison are
the original coefficient maps on the actual AS exchange scheme. The
second arrow follows from ordinary Milnor exact sequences and the proved
positive Chow vanishing; no Witt-complex comparison is assumed here.
-/
noncomputable section
namespace Verification.OriginalIWittComparison
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


variable [PerfectField R] (h2 : (2 : R) ≠ 0)
variable (KM : ℕ → A) (W : A)
variable (IQ : FundamentalIdealCohomologyInput.Theory NT R IP KM W)
variable (IS : FundamentalIdealCohomologyInput.Standard NT R IP KM W IQ CH h2)
local notation "X" => Spec (CommRingCat.of (Global R κ n B))

def comparison (p : ℕ) : NT.cohomology X (IP p) p →+ NT.cohomology X W p := by
  letI := OriginalChowWittIComparison.smooth R κ n B hall hpos hneg hsupport
  exact IQ.toW (Global R κ n B) p p

include C UN N K Neg IS in
theorem comparison_bijective (p : ℕ) (hp : 0 < p) : Function.Bijective
    (comparison R κ n B hall hpos hneg hsupport NT IP KM W IQ p) := by
  letI := OriginalChowWittIComparison.smooth R κ n B hall hpos hneg hsupport
  apply FundamentalIdealChowComparison.toW_bijective NT R h2 IP KM W IQ CH IS (Global R κ n B) p hp
  intro q hq _
  exact OriginalChowWittIComparison.positive_chow R κ n B hall hpos hneg hsupport
    T F RS P Z E U UN N C CH K Neg q hq

def comparisonEquiv (p : ℕ) (hp : 0 < p) : NT.cohomology X (IP p) p ≃+ NT.cohomology X W p :=
  AddEquiv.ofBijective (comparison R κ n B hall hpos hneg hsupport NT IP KM W IQ p)
    (comparison_bijective R κ n B hall hpos hneg hsupport T F RS P Z E U UN N C CH K Neg
      NT IP h2 KM W IQ IS p hp)

theorem comparisonEquiv_apply (p : ℕ) (hp : 0 < p) (a : NT.cohomology X (IP p) p) :
    comparisonEquiv R κ n B hall hpos hneg hsupport T F RS P Z E U UN N C CH K Neg
      NT IP h2 KM W IQ IS p hp a =
      comparison R κ n B hall hpos hneg hsupport NT IP KM W IQ p a := rfl

def chowWittEquiv (p : ℕ) (hp : 0 < p) : CW X p ≃+ NT.cohomology X W p :=
  (OriginalChowWittIComparison.comparisonEquiv R κ n B hall hpos hneg hsupport
    T F RS P Z E U UN N C CH K Neg NT IP CW Q HW p hp).trans
    (comparisonEquiv R κ n B hall hpos hneg hsupport T F RS P Z E U UN N C CH K Neg
      NT IP h2 KM W IQ IS p hp)

theorem chowWittEquiv_apply (p : ℕ) (hp : 0 < p) (a : CW X p) :
    chowWittEquiv R κ n B hall hpos hneg hsupport T F RS P Z E U UN N C CH K Neg
      NT IP CW Q HW h2 KM W IQ IS p hp a =
    comparison R κ n B hall hpos hneg hsupport NT IP KM W IQ p
      (OriginalChowWittIComparison.comparison R κ n B hall hpos hneg hsupport CH NT IP CW Q p a) := rfl

#print axioms comparison
#print axioms comparison_bijective
#print axioms comparisonEquiv
#print axioms comparisonEquiv_apply
#print axioms chowWittEquiv
#print axioms chowWittEquiv_apply
end Verification.OriginalIWittComparison
