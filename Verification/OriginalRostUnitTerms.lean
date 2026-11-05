/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalChowRow
import Verification.RostWeightZero

/-!
# Original Rost Unit Terms

Ordinary K^M_1 sections are units on a smooth affine scheme. Applying
that B-free convention to the proved tame original strata identifies the
literal next-to-last support-row term with the original stratum unit groups.
No formula for their residue differential is assumed in this module.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalRostUnitTerms
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentChartIndex
variable (T : RostAffineInput.Theory)
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)

structure UnitsConvention where
  units : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A],
    (T.cycles (Spec (CommRingCat.of A)) 1).homology 0 ≅ AddCommGrp.of (Additive Aˣ)

variable (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable {m : ℕ} (sm : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)) (Other n I⊕κ) m)
variable (he : ∀ i,IsUnit ((sm.a i).natAbs : R))

include hpos hneg hsupport hI hf he in
theorem stratum_smooth : Algebra.Smooth R (GlobalNormalFrame.ZeroLayer R κ n I B) := by
  letI := ActualTransversePairSmooth.fiber_smooth_tame R (Selected n I) (Other n I⊕κ)
    (Other n I) (matrix κ n I B) hf sm he
  letI : Algebra.Smooth
    (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I⊕κ)
      (Other n I) (matrix κ n I B)))
    (MvPolynomial (Selected n I) (ExchangeTransverseSlice.Fiber
      (ActualOpenChart.characters R (Selected n I) (Other n I⊕κ) (Other n I) (matrix κ n I B)))) := {}
  letI := Algebra.Smooth.comp R
    (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I⊕κ)
      (Other n I) (matrix κ n I B)))
    (MvPolynomial (Selected n I) (ExchangeTransverseSlice.Fiber
      (ActualOpenChart.characters R (Selected n I) (Other n I⊕κ) (Other n I) (matrix κ n I B))))
  exact Algebra.Smooth.of_equiv
    (IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI).symm

def stratumUnits (U : UnitsConvention T) :
    (T.cycles (Spec (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I B))) 1).homology 0 ≅
      AddCommGrp.of (Additive (GlobalNormalFrame.ZeroLayer R κ n I B)ˣ) := by
  letI := stratum_smooth R κ n B hpos hneg hsupport I hI hf sm he
  exact U.units R (GlobalNormalFrame.ZeroLayer R κ n I B)

variable (hall : ∀ I,Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (htame : ∀ I,Independent (laterWeights κ n B) I →
  ∃ (m : ℕ) (sm : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I))
    (Other n I⊕κ) m),∀ i,IsUnit ((sm.a i).natAbs : R))

def predecessorIso (U : UnitsConvention T) (p : ℕ) (hp : 0<p)
    (D : RostSupportInput.Data T (Global R κ n B) (Fin n)
      (fun i => initial R κ n B (Sum.inl i)) (Independent (laterWeights κ n B)) p) :
    D.row.X (p-1) ≅ AddCommGrp.of
      (∀ I : PrimeLayerCover.Index (Independent (laterWeights κ n B)) (p-1),
        Additive (GlobalNormalFrame.ZeroLayer R κ n I.val B)ˣ) := by
  refine D.rowTerm (p-1) ≪≫ ?_
  apply AddEquiv.toAddCommGrpIso
  apply AddEquiv.piCongrRight
  intro I
  have hw : (p:ℤ)-((p-1:ℕ):ℤ)=1 := by omega
  dsimp only
  let m := (htame I.val I.property.2).choose
  let sm := (htame I.val I.property.2).choose_spec.choose
  have he := (htame I.val I.property.2).choose_spec.choose_spec
  have hi := (stratumUnits T R κ n B hpos hneg hsupport I.val I.property.2
    (hall I.val I.property.2) sm he U).addCommGroupIsoToAddEquiv
  have hc : (T.cycles (Spec (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I.val B)))
      ((p:ℤ)-((p-1:ℕ):ℤ))).homology 0 =
    (T.cycles (Spec (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I.val B))) 1).homology 0 :=
    congrArg (fun s => (T.cycles (Spec (CommRingCat.of
      (GlobalNormalFrame.ZeroLayer R κ n I.val B))) s).homology 0) hw
  exact (eqToIso hc).addCommGroupIsoToAddEquiv.trans hi

#print axioms UnitsConvention
#print axioms stratum_smooth
#print axioms stratumUnits
#print axioms predecessorIso
end Verification.OriginalRostUnitTerms
