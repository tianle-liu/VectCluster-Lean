/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalChowBoundaryExpansion
import Verification.RostReducedDivisorResidues
import Verification.OriginalBoundaryBranches

/-!
# Original Chow Boundary Residues

Ordinary generic residues on the literal incoming Chow map, with
constructed adjacent coordinates and the repaired component comparison.
-/
noncomputable section
namespace Verification.OriginalChowBoundaryResidues
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open Classical
open CategoryTheory AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentChartIndex
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
local notation "A" => Global R κ n B
local notation "xs" => (initial R κ n B ∘ Sum.inl)
local notation "Allowed" => Independent (laterWeights κ n B)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I → Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (htame : ∀ I, Independent (laterWeights κ n B) I →
  ∃ (m : ℕ) (sm : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I))
    (Other n I ⊕ κ) m), ∀ i, IsUnit ((sm.a i).natAbs : R))


variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (S : RostSupportInput.Theory T) (P : RostPrincipalLocalizationInput.Theory T)
variable (Z : RostWeightZero.IntegralConvention T)
variable (E : RostCanonicalCoefficients.GenericZeroEvaluation T F Z)
variable (U : OriginalRostUnitTerms.UnitsConvention T)
variable (UN : RostCanonicalCoefficients.UnitsNaturality T F U)
variable (C : OriginalRostBoundaryCharts.Standard R κ n B hpos hneg hsupport hf htame T S P)


variable (p : ℕ) (I : PrimeLayerCover.Index (Independent (laterWeights κ n B)) p)
variable (J : PrimeLayerCover.Index (Independent (laterWeights κ n B)) (p+1))
variable (v : J.val) (h : I.val = J.val.erase v.val)

def coordinates : RostSupportDivisorInput.Coordinates A (Fin n) xs I.val J.val v :=
  h ▸ OriginalRostBoundaryCharts.coordinates R κ n B J.val v

include hpos hneg hsupport hf htame in
theorem face_noetherian : IsNoetherianRing (RostSupportDivisorInput.Face A (Fin n) xs J.val v) := by
  letI := OriginalRostBoundaryCharts.face_smooth R κ n B hpos hneg hsupport hf htame J.val J.property.2 v
  exact Algebra.FiniteType.isNoetherianRing R _

include C UN in
theorem single_residue
    (j : (OriginalRostComponentTerms.decomposition R κ n B hpos hneg hsupport hf htame J.val J.property.2).Index)
    (u : Additive (GlobalNormalFrame.ZeroLayer R κ n I.val B)ˣ) :
    letI := OriginalRostBoundaryValues.source_smooth R κ n B hpos hneg hsupport hf htame I.val I.property.2
    letI := OriginalRostBoundaryCharts.face_smooth R κ n B hpos hneg hsupport hf htame J.val J.property.2 v
    letI := OriginalRostBoundaryValues.open_smooth R κ n B hpos hneg hsupport hf htame J.val J.property.2 v
    let e := coordinates R κ n B p I J v h
    let D := OriginalRostComponentTerms.decomposition R κ n B hpos hneg hsupport hf htame J.val J.property.2
    OriginalChowIncoming.lastDifferential T F S R κ n B hpos hneg hsupport hf htame U Z (p+1)
      (Nat.zero_lt_succ p) (Pi.single I u) J
      (ConnectedComponents.mk (OriginalRostComponentValues.point R κ n B hpos hneg hsupport hf htame J.val J.property.2 j)) =
    RostReducedDivisorResidues.residue T P F Z E U R
      (RostSupportDivisorInput.Face A (Fin n) xs J.val v)
      (RostSupportDivisorInput.parameter A (Fin n) xs J.val v)
      (OriginalRostBoundaryCharts.face_regular R κ n B hpos hneg hsupport hf J.val J.property.2 v)
      D.Factor (e.target.toRingEquiv.trans D.equiv) j
      (Additive.ofMul (Units.map e.source.toRingEquiv.toMonoidHom (Additive.toMul u))) := by
  letI := OriginalRostBoundaryValues.source_smooth R κ n B hpos hneg hsupport hf htame I.val I.property.2
  letI := OriginalRostBoundaryCharts.face_smooth R κ n B hpos hneg hsupport hf htame J.val J.property.2 v
  letI := OriginalRostBoundaryValues.open_smooth R κ n B hpos hneg hsupport hf htame J.val J.property.2 v
  rw [OriginalChowBoundaryExpansion.single]
  have hh := OriginalRostBoundaryValues.component_value R κ n B hpos hneg hsupport hf htame T F S P Z E U UN C p I J v h j
    ((OriginalChowBoundaryExpansion.sourceUnits T R κ n B hpos hneg hsupport hf htame U p I).inv u)
  simpa only [OriginalChowBoundaryExpansion.sourceUnits,Iso.inv_hom_id_apply] using hh

#print axioms coordinates
#print axioms face_noetherian
#print axioms single_residue
end Verification.OriginalChowBoundaryResidues
