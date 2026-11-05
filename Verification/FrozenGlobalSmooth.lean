/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenAcyclicCover
import Verification.SmoothOpenCover

/-!
# Frozen Global Smooth

The fixed frozen exchange presentation is finitely presented over the
original base. Smoothness of its independent-set charts therefore glues to
actual Algebra.Smooth of that global presentation.
-/
noncomputable section
namespace Verification.FrozenGlobalSmooth
open MvPolynomial Verification.FrozenAcyclicCover Verification.ActualStratum
open Verification.ExchangeOpenCover
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

def scalarMap : R →+* Global R κ n B := (coefficientMap R κ n B).comp C

instance baseAlgebra : Algebra R (Global R κ n B) := (scalarMap R κ n B).toAlgebra

instance scalarTower : IsScalarTower R (PolynomialPresentation R κ n B) (Global R κ n B) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem presentation_finitePresentation : Algebra.FinitePresentation R (PolynomialPresentation R κ n B) := by
  letI : Algebra.FinitePresentation R
      (MvPolynomial (Fin n ⊕ Empty) (OriginalPolynomial R (Fin n) κ)) :=
    Algebra.FinitePresentation.trans R (OriginalPolynomial R (Fin n) κ) _
  exact Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))

theorem global_finitePresentation : Algebra.FinitePresentation R (Global R κ n B) := by
  classical
  letI := presentation_finitePresentation R κ n B
  let r : {k : κ // k ∉ Set.range (noMutable κ)} → PolynomialPresentation R κ n B :=
    fun k => FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B (Sum.inr k.1)
  letI : Algebra.Smooth (PolynomialPresentation R κ n B) (Global R κ n B) :=
    SplitExchangeChart.valueLocalization_smooth r
  exact Algebra.FinitePresentation.trans R (PolynomialPresentation R κ n B) _

theorem global_smooth_of_charts
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
    (hsmooth : ∀ I : {I : Finset (Fin n) // Independent (laterWeights κ n B) I},
      Algebra.Smooth R (Localization.Away
        (chartElement (fun i => initial R κ n B (Sum.inl i)) I.1))) :
    Algebra.Smooth R (Global R κ n B) := by
  letI := global_finitePresentation R κ n B
  exact SmoothOpenCover.smooth_of_basicOpen_cover R (Global R κ n B)
    (fun I : {I : Finset (Fin n) // Independent (laterWeights κ n B) I} =>
      chartElement (fun i => initial R κ n B (Sum.inl i)) I.1)
    (global_charts_cover R κ n B hpos hneg hsupport) hsmooth

#print axioms scalarMap
#print axioms baseAlgebra
#print axioms scalarTower
#print axioms presentation_finitePresentation
#print axioms global_finitePresentation
#print axioms global_smooth_of_charts
end Verification.FrozenGlobalSmooth
