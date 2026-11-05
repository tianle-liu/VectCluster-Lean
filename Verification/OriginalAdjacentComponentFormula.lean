/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalAdjacentUnitResidueFormula
import Verification.OriginalBoundaryComponentMap
import Verification.OriginalComponentExponentCoordinates
import Verification.OriginalChowBoundaryResidues

/-!
# Original Adjacent Component Formula

The adjacent residue at a genuine target component is the exponent
of the deleted vertex at its image under the actual map on components.
The same formula is then proved for a single input of the original Chow
incoming map.
-/
noncomputable section
namespace Verification.OriginalAdjacentComponentFormula
attribute [local instance] Classical.propDecidable
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open scoped BigOperators
open Verification.IndependentChartIndex Verification.FrozenAcyclicCover
open Verification.OriginalFreeTorusCoordinates

theorem sum_indicator_equiv {K C : Type*} [Fintype K] (e : C ≃ K) (a : K → ℤ) (c : C) :
    ∑ i, a i * (if c = e.symm i then (1 : ℤ) else 0) = a (e c) := by
  classical
  rw [Finset.sum_eq_single (e c)]
  · simp
  · intro i hi hne
    have hc : c ≠ e.symm i := by
      intro hc
      apply hne
      simpa only [Equiv.apply_symm_apply] using (congrArg e hc).symm
    rw [if_neg hc, mul_zero]
  · intro hc
    exact False.elim (hc (Finset.mem_univ _))

section Adjacent
variable (T : RostAffineInput.Theory) (P : RostPrincipalLocalizationInput.Theory T)
variable (F : RostFiniteProducts.Standard T) (Z : RostWeightZero.IntegralConvention T)
variable (E : RostCanonicalCoefficients.GenericZeroEvaluation T F Z)
variable (U : OriginalRostUnitTerms.UnitsConvention T)
variable (N : RostPrincipalResidueInput.Normalization T P F Z E U)
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ) (J : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : J)
local notation "I" => J.erase v.val
local notation "Q" => GlobalNormalFrame.ZeroLayer R κ n I B
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hJ : ExchangeOpenCover.Independent (laterWeights κ n B) J)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))
variable {m : ℕ} (sm : Basis.SmithNormalForm
  (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)) (Other n J ⊕ κ) m)
variable (he : ∀ i, IsUnit ((sm.a i).natAbs : R))
variable {K : Type} (D : K → Type) [∀ j, CommRing (D j)] [∀ j, IsDomain (D j)]
variable (de : GlobalNormalFrame.ZeroLayer R κ n J B ≃+* ∀ j, D j) (j : K)
variable (Src : OriginalRetainedProductCoordinates.ProductData R κ n (J.erase v.val) B)
local notation "hI" => OriginalRemainingExtension.old_independent κ n J B v hJ
local notation "b" => OriginalFreeBoundaryIndex.boundary κ n J B v hpos hneg hsupport hJ
local notation "c" => ConnectedComponents.mk (RostComponentEvaluation.point D de j)
local notation "r" => OriginalBoundaryComponentMap.componentMap R κ n J B v hpos hneg hsupport hJ hf Src
local notation "scomp" => OriginalBoundaryComponentMap.sourceComponent R κ n J B v hpos hneg hsupport hJ Src
local notation "ρ" => OriginalBoundaryResidueGenerators.residue T P F Z E U R κ n J B v
  hpos hneg hsupport hJ hf sm he D de j

theorem componentWeight_eq (l : Src.Index) :
    OriginalAdjacentUnitResidueFormula.componentWeight R κ n J B v hpos hneg hsupport hJ hf D de j Src l =
      if r c = scomp l then 1 else 0 := by
  unfold OriginalAdjacentUnitResidueFormula.componentWeight
  rw [OriginalBoundaryComponentMap.closedEquiv_eq_target]
  rw [OriginalBoundaryComponentMap.branch_component_iff R κ n J B v hpos hneg hsupport hJ hf Src D de j l]

include N in
theorem residue (u : Qˣ) :
    ρ (Additive.ofMul u) =
      OriginalComponentExponentCoordinates.exponents R κ n I B Src hpos hneg hsupport hI u v.val (r c) := by
  have heq := OriginalComponentExponentCoordinates.exponents_at R κ n I B Src hpos hneg hsupport hI u b (r c)
  rw [OriginalFreeCoordinateVertex.boundary_vertex] at heq
  rw [heq, OriginalAdjacentUnitResidueFormula.residue T P F Z E U N]
  simp_rw [componentWeight_eq]
  exact sum_indicator_equiv
    (OriginalComponentExponentCoordinates.labels R κ n I B Src hpos hneg hsupport hI)
    (fun l => OriginalStratumUnitGeneration.exponentPart R κ n I B Src hpos hneg hsupport hI u l b) (r c)
end Adjacent

section Incoming
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, ExchangeOpenCover.Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (htame : ∀ I, ExchangeOpenCover.Independent (laterWeights κ n B) I →
  ∃ (m : ℕ) (sm : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I))
    (Other n I ⊕ κ) m), ∀ i, IsUnit ((sm.a i).natAbs : R))
variable (p : ℕ) (J : PrimeLayerCover.Index (ExchangeOpenCover.Independent (laterWeights κ n B)) (p+1))
variable (v : J.val)

def sourceIndex : PrimeLayerCover.Index (ExchangeOpenCover.Independent (laterWeights κ n B)) p :=
  ⟨J.val.erase v.val, by
    constructor
    · rw [Finset.card_erase_of_mem v.property, J.property.1]
      omega
    · exact OriginalRemainingExtension.old_independent κ n J.val B v (And.right (Subtype.property J))⟩

variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (S : RostSupportInput.Theory T) (P : RostPrincipalLocalizationInput.Theory T)
variable (Z : RostWeightZero.IntegralConvention T)
variable (E : RostCanonicalCoefficients.GenericZeroEvaluation T F Z)
variable (U : OriginalRostUnitTerms.UnitsConvention T)
variable (UN : RostCanonicalCoefficients.UnitsNaturality T F U)
variable (N : RostPrincipalResidueInput.Normalization T P F Z E U)
variable (C : OriginalRostBoundaryCharts.Standard R κ n B hpos hneg hsupport hf htame T S P)
variable (Src : OriginalRetainedProductCoordinates.ProductData R κ n (J.val.erase v.val) B)
local notation "idx" => sourceIndex κ n B p J v
local notation "hI" => OriginalRemainingExtension.old_independent κ n J.val B v (And.right (Subtype.property J))
local notation "TargetData" => OriginalRostComponentTerms.decomposition R κ n B hpos hneg hsupport hf htame J.val (And.right (Subtype.property J))
local notation "r" => OriginalBoundaryComponentMap.componentMap R κ n J.val B v hpos hneg hsupport (And.right (Subtype.property J))
  (hf J.val (And.right (Subtype.property J))) Src

include C UN N in
theorem single (j : (TargetData).Index)
    (u : (GlobalNormalFrame.ZeroLayer R κ n (J.val.erase v.val) B)ˣ) :
    OriginalChowIncoming.lastDifferential T F S R κ n B hpos hneg hsupport hf htame U Z (p+1)
      (Nat.zero_lt_succ p) (Pi.single idx (Additive.ofMul u)) J
      (ConnectedComponents.mk (OriginalRostComponentValues.point R κ n B hpos hneg hsupport hf htame J.val (And.right (Subtype.property J)) j)) =
    OriginalComponentExponentCoordinates.exponents R κ n (J.val.erase v.val) B Src hpos hneg hsupport hI u v.val
      (r (ConnectedComponents.mk (OriginalRostComponentValues.point R κ n B hpos hneg hsupport hf htame J.val (And.right (Subtype.property J)) j))) := by
  obtain ⟨m,sm,he⟩ := htame J.val (And.right (Subtype.property J))
  have h := OriginalChowBoundaryResidues.single_residue R κ n B hpos hneg hsupport hf htame
    T F S P Z E U UN C p idx J v rfl j (Additive.ofMul u)
  calc
    _ = OriginalBoundaryResidueGenerators.residue T P F Z E U R κ n J.val B v
        hpos hneg hsupport (And.right (Subtype.property J)) (hf J.val (And.right (Subtype.property J))) sm he
        (TargetData).Factor (TargetData).equiv j (Additive.ofMul u) := h
    _ = _ := residue T P F Z E U N R κ n J.val B v hpos hneg hsupport (And.right (Subtype.property J))
      (hf J.val (And.right (Subtype.property J))) sm he (TargetData).Factor (TargetData).equiv j Src u
end Incoming

#print axioms sum_indicator_equiv
#print axioms componentWeight_eq
#print axioms residue
#print axioms sourceIndex
#print axioms single
end Verification.OriginalAdjacentComponentFormula
