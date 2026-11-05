/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalASComponentVanishing
import Verification.OriginalChowComponentCokernel

/-!
# Original AS Chow Vanishing

Under the original AS hypothesis, every positive Chow group of the
actual exchange scheme vanishes. Rank, tame Smith factors, connected
strata, and surjectivity of every component block are proved internally;
only the uniform cycle-module and Chow comparison inputs remain.
-/
noncomputable section
namespace Verification.OriginalASChowVanishing
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry
open Verification.IndependentChartIndex Verification.FrozenAcyclicCover
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hall : ∀ I, ExchangeOpenCover.Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun a i => B a (Sum.inl i)) I)

include hall in
theorem selected_injective : ∀ I, ExchangeOpenCover.Independent (laterWeights κ n B) I →
    Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I) :=
  fun I hI => ((GlobalSelectedColumns.AS_iff κ n B I).mpr (hall I hI)).1

include hall in
theorem tame : ∀ I, ExchangeOpenCover.Independent (laterWeights κ n B) I →
    ∃ (m : ℕ) (sm : Basis.SmithNormalForm
      (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)) (Other n I ⊕ κ) m),
      ∀ i, IsUnit ((sm.a i).natAbs : R) := by
  intro I hI
  obtain ⟨m,sm⟩ := (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)).smithNormalForm Finsupp.basisSingleOne
  refine ⟨m,sm,?_⟩
  have hs := ((GlobalSelectedColumns.AS_iff κ n B I).mpr (hall I hI)).2
  simp only [SaturatedSmith.coefficient_natAbs sm hs, Nat.cast_one, isUnit_one, implies_true]

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (S : RostSupportInput.Theory T) (P : RostPrincipalLocalizationInput.Theory T)
variable (Z : RostWeightZero.IntegralConvention T)
variable (E : RostCanonicalCoefficients.GenericZeroEvaluation T F Z)
variable (U : OriginalRostUnitTerms.UnitsConvention T)
variable (UN : RostCanonicalCoefficients.UnitsNaturality T F U)
variable (N : RostPrincipalResidueInput.Normalization T P F Z E U)
variable (C : OriginalRostBoundaryCharts.Standard R κ n B hpos hneg hsupport
  (selected_injective κ n B hall) (tame R κ n B hall) T S P)
variable (CH : Scheme → ℕ → AddCommGrp)
variable (K : RostMilnorInput.ChowComparison T CH) (Neg : RostMilnorInput.NegativeWeights T)

include C UN N K Neg in
theorem positive_subsingleton (p : ℕ) :
    Subsingleton (CH (Spec (CommRingCat.of (Global R κ n B))) (p+1)) := by
  let hf := selected_injective κ n B hall
  let htame := tame R κ n B hall
  let D := OriginalChowRetainedData.family R κ n B hf htame p
  let r := OriginalChowWholeBoundary.componentMap R κ n B hpos hneg hsupport hf p D
  letI (J : AllowedComponentRow.Target (ExchangeOpenCover.Independent (laterWeights κ n B)) p) :
      Subsingleton (OriginalChowComponentCokernel.ComponentCokernel R κ n B hpos hneg hsupport hf p D J) :=
    OriginalASComponentVanishing.actual_jointPullback_cokernel R κ n B hpos hneg hsupport p r J
      (hall J.val J.property.2)
  exact (OriginalChowComponentCokernel.canonicalChowIso R κ n B hpos hneg hsupport hf htame p
    T F S P Z E U UN N C CH K Neg).addCommGroupIsoToAddEquiv.injective.subsingleton

include C UN N K Neg in
theorem positive_eq_zero (p : ℕ)
    (x : CH (Spec (CommRingCat.of (Global R κ n B))) (p+1)) : x = 0 := by
  letI := positive_subsingleton R κ n B hall hpos hneg hsupport T F S P Z E U UN N C CH K Neg p
  exact Subsingleton.elim _ _

#print axioms selected_injective
#print axioms tame
#print axioms positive_subsingleton
#print axioms positive_eq_zero
end Verification.OriginalASChowVanishing
