/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalRostUnitTerms
import Verification.OriginalRostComponentTerms

/-!
# Original Chow Incoming

A cokernel presentation of the actual Chow group with its source
literally the original stratum units and its target literally the functions
on actual connected components. The map retains the real support-row
boundary; replacing it by the article's component-pullback matrix requires
and is not confused with a separate residue-compatibility theorem.
-/
noncomputable section
namespace Verification.OriginalChowIncoming
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentChartIndex
variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (S : RostSupportInput.Theory T)
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hf : ∀ I,Independent (laterWeights κ n B) I → Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (htame : ∀ I,Independent (laterWeights κ n B) I →
  ∃ (m : ℕ) (sm : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I))
    (Other n I⊕κ) m),∀ i,IsUnit ((sm.a i).natAbs : R))

variable (CH : Scheme → ℕ → AddCommGrp) (K : RostMilnorInput.ChowComparison T CH)


variable (U : OriginalRostUnitTerms.UnitsConvention T)
variable (Z : RostWeightZero.IntegralConvention T)
variable (p : ℕ) (hp : 0<p)

local notation "D" => OriginalRostSupport.support T S R κ n B hpos hneg hsupport hf htame p
local notation "E₁" => OriginalRostUnitTerms.predecessorIso T R κ n B hpos hneg hsupport hf htame U p hp (D)
local notation "E₀" => OriginalRostComponentTerms.terminalIso T F R κ n B hpos hneg hsupport hf htame Z p (D)

abbrev UnitsTerm := AddCommGrp.of
  (∀ I : PrimeLayerCover.Index (Independent (laterWeights κ n B)) (p-1),
    Additive (GlobalNormalFrame.ZeroLayer R κ n I.val B)ˣ)
abbrev ComponentsTerm := AddCommGrp.of
  (∀ I : PrimeLayerCover.Index (Independent (laterWeights κ n B)) p,
    ConnectedComponents (PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n I.val B))→ℤ)

def lastDifferential : UnitsTerm R κ n B p ⟶ ComponentsTerm R κ n B p :=
  (E₁).inv ≫ (D).row.d (p-1) p ≫ (E₀).hom

theorem differential_square : (D).row.d (p-1) p ≫ (E₀).hom =
    (E₁).hom ≫ lastDifferential T F S R κ n B hpos hneg hsupport hf htame U Z p hp := by
  simp only [lastDifferential,Iso.hom_inv_id_assoc]

def chowCokernelIso (N : RostMilnorInput.NegativeWeights T) :
    CH (Spec (CommRingCat.of (Global R κ n B))) p ≅
      cokernel (lastDifferential T F S R κ n B hpos hneg hsupport hf htame U Z p hp) :=
  OriginalChowRow.chowQuotientIso T F S R κ n B hpos hneg hsupport hf htame CH K N p hp ≪≫
    (AddCommGrp.cokernelIsoQuotient ((D).row.d (p-1) p)).symm ≪≫
    cokernel.mapIso ((D).row.d (p-1) p)
      (lastDifferential T F S R κ n B hpos hneg hsupport hf htame U Z p hp) (E₁) (E₀)
      (differential_square T F S R κ n B hpos hneg hsupport hf htame U Z p hp)

#print axioms UnitsTerm
#print axioms ComponentsTerm
#print axioms lastDifferential
#print axioms differential_square
#print axioms chowCokernelIso
end Verification.OriginalChowIncoming
