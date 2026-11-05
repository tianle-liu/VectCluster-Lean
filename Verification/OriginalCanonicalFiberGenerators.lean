/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalCanonicalFiberProjection
import Verification.ExplicitStratumCoordinates

/-!
# Original Canonical Fiber Generators

The literal remaining original coordinates under the canonical fiber
projection of an actual zero layer.
-/
noncomputable section
namespace Verification.OriginalCanonicalFiberGenerators
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.IndependentBasicOpen Verification.ExchangeOpenCover
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hI : Independent (laterWeights κ n B) I)

theorem original (a : AnticliqueSubcolumns.Rows (C := κ) I) :
    OriginalCanonicalFiberProjection.projection R κ n I B hpos hneg hsupport hI
      (ExplicitStratumCoordinates.original R κ n I B a.val)=
    Ideal.Quotient.mk (ExchangeTransverseSlice.fiberIdeal
      (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B)))
        (OriginalTorus.torusCoordinate R (Other n I ⊕ κ) (GlobalSelectedColumns.rowEquiv κ n I a)) := by
  change PolynomialSectionIso.zeroEvaluation R _ _
    (IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI
      (ExplicitStratumCoordinates.original R κ n I B a.val))=_
  rw [ExplicitStratumCoordinates.affineEquiv_original]
  exact MvPolynomial.aeval_C _ _

theorem outside (k : Other n I ⊕ κ) :
    OriginalCanonicalFiberProjection.projection R κ n I B hpos hneg hsupport hI
      (ExplicitStratumCoordinates.original R κ n I B ((originals κ n I).symm (Sum.inr k)))=
    Ideal.Quotient.mk (ExchangeTransverseSlice.fiberIdeal
      (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B)))
        (OriginalTorus.torusCoordinate R (Other n I ⊕ κ) k) := by
  let a := (GlobalSelectedColumns.rowEquiv κ n I).symm k
  have ha : (originals κ n I).symm (Sum.inr k)=a.val := by
    apply (originals κ n I).injective
    rw [Equiv.apply_symm_apply,ExplicitStratumCoordinates.row_originals]
    exact congrArg Sum.inr (Equiv.apply_symm_apply _ _).symm
  rw [ha,original]
  congr 2
  exact Equiv.apply_symm_apply _ _

#print axioms original
#print axioms outside
end Verification.OriginalCanonicalFiberGenerators
