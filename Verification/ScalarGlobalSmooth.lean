/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarIndependentBasicOpen
import Verification.ScalarActualOpenGeometry
import Verification.GlobalExchangeSmooth

/-!
# Scalar Global Smooth

Actual global scalar exchange rings are smooth under the AS conditions
on every independent set. The cover and its local presentations are proved
for the same frozen localization; there is no whole-matrix rank premise.
-/
noncomputable section
namespace Verification.ScalarGlobalSmooth
open MvPolynomial Verification.ScalarFrozenGlobal Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.FrozenAcyclicCover
open Verification.GlobalExchangeSmooth (selectedMap)
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem presentation_finitePresentation : Algebra.FinitePresentation R (Presentation R κ n B a b) := by
  letI : Algebra.FinitePresentation R
      (MvPolynomial (Fin n ⊕ Empty) (ActualStratum.OriginalPolynomial R (Fin n) κ)) :=
    Algebra.FinitePresentation.trans R (ActualStratum.OriginalPolynomial R (Fin n) κ) _
  exact Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))

theorem global_finitePresentation : Algebra.FinitePresentation R (ScalarFrozenGlobal.Global R κ n B a b) := by
  letI := presentation_finitePresentation R κ n B a b
  let r : κ → Presentation R κ n B a b := fun k => original R κ n B a b (Sum.inr k)
  letI : Algebra.Smooth (Presentation R κ n B a b) (ScalarFrozenGlobal.Global R κ n B a b) :=
    SplitExchangeChart.valueLocalization_smooth r
  exact Algebra.FinitePresentation.trans R (Presentation R κ n B a b) _

variable (hpos : ∀ r i : Fin n, ¬ r < i → (B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ r i : Fin n, ¬ i < r → (-B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
include hpos hneg hsupport

theorem basicOpen_smooth (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I)
    (hf : Function.Injective (selectedMap κ n B I))
    (hs : FreezingLattice.Saturated (LinearMap.range (selectedMap κ n B I))) :
    Algebra.Smooth R (ScalarIndependentBasicOpen.BasicOpen R κ n I B a b) := by
  letI := ScalarActualOpenGeometry.globalOpen_smooth R (Selected n I) (Other n I ⊕ κ) (Other n I)
    (ScalarIndependentChartPresentation.newScalar R n I a)
    (ScalarIndependentChartPresentation.newScalar R n I b) Sum.inl (matrix κ n I B)
    (matrix_zero_block κ n I B hpos hneg hsupport hI) hf hs
  exact Algebra.Smooth.of_equiv (ScalarIndependentBasicOpen.chartEquiv R κ n I B a b).symm

theorem global_smooth_saturated
    (hf : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
      Function.Injective (selectedMap κ n B I))
    (hs : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
      FreezingLattice.Saturated (LinearMap.range (selectedMap κ n B I))) :
    Algebra.Smooth R (ScalarFrozenGlobal.Global R κ n B a b) := by
  letI := global_finitePresentation R κ n B a b
  apply SmoothOpenCover.exchange_smooth_of_charts R (ScalarFrozenGlobal.Global R κ n B a b)
    (earlierWeights κ n B) (laterWeights κ n B)
    (fun i => ScalarFrozenGlobal.initial R κ n B a b (Sum.inl i)) (ScalarFrozenGlobal.mutated R κ n B a b)
    (ScalarFrozenGlobal.earlierCoefficient R κ n B a b) (ScalarFrozenGlobal.laterCoefficient R κ n B a b)
    hsupport (earlierCoefficient_unit R κ n B a b) (ordered_equations R κ n B a b hpos hneg)
  intro I
  exact basicOpen_smooth R κ n B a b hpos hneg hsupport I.1 I.2 (hf I.1 I.2) (hs I.1 I.2)

#print axioms presentation_finitePresentation
#print axioms global_finitePresentation
#print axioms basicOpen_smooth
#print axioms global_smooth_saturated
end Verification.ScalarGlobalSmooth
