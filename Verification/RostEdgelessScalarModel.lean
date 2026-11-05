/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalEdgelessStandard
import Verification.ScalarIndependentBasicOpen
import Verification.ScalarActualOpenGeometry
import Verification.ScalarLocalExchange

/-!
# Rost Edgeless Scalar Model

Unit scalar coefficients in an edgeless original presentation are
removed by the actual primitive torus translation. This includes the
nonzero scalar case of the manuscript's edgeless assertion.
-/
noncomputable section
namespace Verification.RostEdgelessScalarModel
open Verification.OriginalEdgelessGeometry Verification.OriginalEdgelessStandard
open Verification.IndependentChartIndex Verification.LocalExchangeSmooth
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev leftScalar := ScalarIndependentChartPresentation.newScalar R n Finset.univ a
abbrev rightScalar := ScalarIndependentChartPresentation.newScalar R n Finset.univ b
abbrev scalarRatio (i : Vertices n) := leftScalar R n a (Sum.inl i) * (rightScalar R n b (Sum.inl i))⁻¹
abbrev scalarCharacters := ScalarActualOpenChart.characters R (Vertices n) (Rows κ n)
  (Other n Finset.univ) (leftScalar R n a) (rightScalar R n b) (matrix κ n Finset.univ B)

theorem chartValue_one : ScalarIndependentBasicOpen.chartValue R κ n Finset.univ B a b = 1 := by
  classical
  simp [ScalarIndependentBasicOpen.chartValue, ExchangeOpenCover.chartElement]

def wholeChart : ScalarFrozenGlobal.Global R κ n B a b ≃ₐ[R]
    ScalarIndependentBasicOpen.BasicOpen R κ n Finset.univ B a b :=
  (IsLocalization.atUnit (ScalarFrozenGlobal.Global R κ n B a b)
    (ScalarIndependentBasicOpen.BasicOpen R κ n Finset.univ B a b)
    (ScalarIndependentBasicOpen.chartValue R κ n Finset.univ B a b)
    ((chartValue_one R κ n B a b).symm ▸ isUnit_one)).restrictScalars R

variable (hAS : AnticliqueSubcolumns.AS (fun v i => B v (Sum.inl i)) Finset.univ)
variable (hzero : ∀ v i : Fin n, B (Sum.inl v) (Sum.inl i) = 0)

def characterEquiv : LocalAlgebra (scalarCharacters R κ n B a b) ≃ₐ[R]
    LocalAlgebra (characterUnits R (columns κ n B)) :=
  (LocalExchangeTransport.localEquiv
    (AlgEquiv.refl : CharacterMapSmooth.Torus R (Rows κ n →₀ ℤ) ≃ₐ[R] _)
    (scalarCharacters R κ n B a b)
    (ScalarLocalExchange.scalarUnits (columns κ n B) (scalarRatio R n a b))
    (fun i => congrArg Units.val (congrFun
      (ScalarActualOpenGeometry.characters_eq R (Vertices n) (Rows κ n) (Other n Finset.univ)
        (leftScalar R n a) (rightScalar R n b) (matrix κ n Finset.univ B)) i))).trans
    (((ScalarLocalExchange.scalarEquiv (columns κ n B)
      ((GlobalSelectedColumns.AS_iff κ n B Finset.univ).mpr hAS).1
      ((GlobalSelectedColumns.AS_iff κ n B Finset.univ).mpr hAS).2
      (scalarRatio R n a b)).restrictScalars R).symm)

def standardEquiv : ScalarFrozenGlobal.Global R κ n B a b ≃ₐ[R] StandardModel R κ n :=
  (((((wholeChart R κ n B a b).trans
    (ScalarIndependentBasicOpen.chartEquiv R κ n Finset.univ B a b)).trans
    (ScalarActualOpenChart.globalOpenEquiv R (Vertices n) (Rows κ n) (Other n Finset.univ)
      (leftScalar R n a) (rightScalar R n b) Sum.inl (matrix κ n Finset.univ B)
      (fun v i => hzero v.val i.val))).trans (characterEquiv R κ n B a b hAS)).trans
    (PrimitiveExchangeSplit.asChart R (columns κ n B)
      ((GlobalSelectedColumns.AS_iff κ n B Finset.univ).mpr hAS).1
      ((GlobalSelectedColumns.AS_iff κ n B Finset.univ).mpr hAS).2)).trans
    (UniversalExchangeTransport.openEquiv (complementTorus R κ n B hAS) (verticesEquiv n))

#print axioms leftScalar
#print axioms rightScalar
#print axioms scalarRatio
#print axioms scalarCharacters
#print axioms chartValue_one
#print axioms wholeChart
#print axioms characterEquiv
#print axioms standardEquiv
end Verification.RostEdgelessScalarModel
