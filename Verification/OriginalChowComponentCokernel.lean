/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalChowWholeBoundary
import Verification.ChowLinearCokernel
import Verification.OriginalChowRetainedData
import Mathlib.Algebra.DirectSum.Module

/-!
# Original Chow Component Cokernel

The actual positive Chow group is the finite product of component
pullback cokernels. The real incoming differential is used; its image is
computed from proved residues and explicitly realized integer exponents.
-/
noncomputable section
namespace Verification.OriginalChowComponentCokernel
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open Classical
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators DirectSum
open Verification.IndependentChartIndex Verification.FrozenAcyclicCover
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
variable (p : ℕ)
local notation "Allowed" => ExchangeOpenCover.Independent (laterWeights κ n B)
local notation "Source" => AllowedComponentRow.Source Allowed p
local notation "Target" => AllowedComponentRow.Target Allowed p
local notation "pred" => AllowedComponentRow.predecessor Allowed (OriginalChowExponentFamily.hereditary κ n B) p
variable (D : ∀ I : AllowedComponentRow.Source (ExchangeOpenCover.Independent (laterWeights κ n B)) p,
  OriginalRetainedProductCoordinates.ProductData R κ n I.val B)

variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (S : RostSupportInput.Theory T) (P : RostPrincipalLocalizationInput.Theory T)
variable (Z : RostWeightZero.IntegralConvention T)
variable (E : RostCanonicalCoefficients.GenericZeroEvaluation T F Z)
variable (U : OriginalRostUnitTerms.UnitsConvention T)
variable (UN : RostCanonicalCoefficients.UnitsNaturality T F U)
variable (N : RostPrincipalResidueInput.Normalization T P F Z E U)
variable (C : OriginalRostBoundaryCharts.Standard R κ n B hpos hneg hsupport hf htame T S P)
local notation "δ" => OriginalChowIncoming.lastDifferential T F S R κ n B hpos hneg hsupport hf htame U Z (p+1) (Nat.zero_lt_succ p)
local notation "r" => OriginalChowWholeBoundary.componentMap R κ n B hpos hneg hsupport hf p D

local notation "PC" => OriginalChowExponentFamily.componentFamily R κ n B p
local notation "QC" => OriginalChowExponentFamily.componentFamily R κ n B (p+1)
local notation "H" => OriginalChowExponentFamily.hereditary κ n B

def block (J : Target) := AllowedComponentRow.jointPullback Allowed H p PC QC r J

abbrev ComponentCokernel (J : Target) := (QC J → ℤ) ⧸ LinearMap.range
  (block R κ n B hpos hneg hsupport hf p D J)

include C UN N in
theorem range_eq : LinearMap.range (δ).hom.toIntLinearMap =
    Submodule.pi Set.univ (fun J : Target => LinearMap.range
      (block R κ n B hpos hneg hsupport hf p D J)) := by
  change LinearMap.range (δ).hom.toIntLinearMap =
    Submodule.pi Set.univ (fun J => LinearMap.range (AllowedComponentRow.jointPullback Allowed H p PC QC r J))
  rw [← AllowedComponentRow.range_blockMap Allowed H p PC QC r]
  ext y
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨OriginalChowExponentFamily.flags R κ n B p D hpos hneg hsupport u,
      (OriginalChowWholeBoundary.blockMap_eq R κ n B hpos hneg hsupport hf htame p D
        T F S P Z E U UN N C u).symm⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨u,hu⟩ := OriginalChowExponentFamily.flags_surjective R κ n B p D hpos hneg hsupport a
    refine ⟨u, ?_⟩
    change δ u = _
    rw [OriginalChowWholeBoundary.blockMap_eq R κ n B hpos hneg hsupport hf htame p D
      T F S P Z E U UN N C u, hu]

def quotientEquiv :
    ((OriginalChowIncoming.ComponentsTerm R κ n B (p+1)) ⧸ LinearMap.range (δ).hom.toIntLinearMap) ≃ₗ[ℤ]
      (∀ J : Target, ComponentCokernel R κ n B hpos hneg hsupport hf p D J) := by
  classical
  letI : Fintype Target := Fintype.ofFinite _
  exact (Submodule.quotEquivOfEq _ _
    (range_eq R κ n B hpos hneg hsupport hf htame p D T F S P Z E U UN N C)).trans
      (Submodule.quotientPi (fun J => LinearMap.range (block R κ n B hpos hneg hsupport hf p D J)))

variable (CH : AlgebraicGeometry.Scheme → ℕ → AddCommGrp)
variable (K : RostMilnorInput.ChowComparison T CH) (Neg : RostMilnorInput.NegativeWeights T)

def chowIso : CH (AlgebraicGeometry.Spec (CommRingCat.of (Global R κ n B))) (p+1) ≅
    AddCommGrp.of (∀ J : Target, ComponentCokernel R κ n B hpos hneg hsupport hf p D J) :=
  OriginalChowIncoming.chowCokernelIso T F S R κ n B hpos hneg hsupport hf htame CH K U Z
    (p+1) (Nat.zero_lt_succ p) Neg ≪≫
  ChowLinearCokernel.quotientIso (δ) ≪≫
  (quotientEquiv R κ n B hpos hneg hsupport hf htame p D T F S P Z E U UN N C).toAddEquiv.toAddCommGrpIso

def canonicalChowIso : CH (AlgebraicGeometry.Spec (CommRingCat.of (Global R κ n B))) (p+1) ≅
    AddCommGrp.of (∀ J : Target, ComponentCokernel R κ n B hpos hneg hsupport hf p
      (OriginalChowRetainedData.family R κ n B hf htame p) J) :=
  chowIso R κ n B hpos hneg hsupport hf htame p
    (OriginalChowRetainedData.family R κ n B hf htame p) T F S P Z E U UN N C CH K Neg

def directSumChowIso : CH (AlgebraicGeometry.Spec (CommRingCat.of (Global R κ n B))) (p+1) ≅
    AddCommGrp.of (⨁ (J : Target), ComponentCokernel R κ n B hpos hneg hsupport hf p
      (OriginalChowRetainedData.family R κ n B hf htame p) J) := by
  classical
  letI : Fintype Target := Fintype.ofFinite _
  exact canonicalChowIso R κ n B hpos hneg hsupport hf htame p T F S P Z E U UN N C CH K Neg ≪≫
    (DirectSum.linearEquivFunOnFintype ℤ Target (fun J =>
      ComponentCokernel R κ n B hpos hneg hsupport hf p
        (OriginalChowRetainedData.family R κ n B hf htame p) J)).symm.toAddEquiv.toAddCommGrpIso

#print axioms block
#print axioms ComponentCokernel
#print axioms range_eq
#print axioms quotientEquiv
#print axioms chowIso
#print axioms canonicalChowIso
#print axioms directSumChowIso
end Verification.OriginalChowComponentCokernel
