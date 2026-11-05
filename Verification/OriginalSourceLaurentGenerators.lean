/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalSourceTorusGenerators
import Verification.OriginalCanonicalFiberGenerators
import Verification.ActualLaurentSheafBaseChange
import Verification.LaurentPolynomialUniversal

/-!
# Original Source Laurent Generators

The actual adjacent source map sends its normal original coordinate to
the Laurent parameter and every remaining original coordinate to its literal
target-fiber projection.
-/
noncomputable section
namespace Verification.OriginalSourceLaurentGenerators
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.IndependentBasicOpen Verification.ExchangeOpenCover
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (J : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Selected n J)
variable (hD : ∀ l i : Selected n J, matrix κ n J B (Sum.inl l) (Sum.inl i)=0)
local notation "Sel" => Selected n J
local notation "Rest" => Other n J
local notation "D" => matrix κ n J B
local notation "χ" => ActualOpenChart.characters R Sel (Rest ⊕ κ) Rest D
local notation "New" => ExchangeTransverseSlice.Fiber χ

def map : GlobalNormalFrame.ZeroLayer R κ n (J.erase v.val) B →ₐ[R] LaurentBasepoint.Laurent New :=
  (ActualTorusFace.torusFace R Sel (Rest ⊕ κ) Rest D v).comp
    (OriginalSourceCoefficientCoordinates.torusMap R κ n J B v hD)

theorem parameter : map R κ n J B v hD
    (ExplicitStratumCoordinates.original R κ n (J.erase v.val) B (Sum.inl v.val))=
      LaurentPolynomialUniversal.parameter New := by
  change ActualTorusFace.torusFace R Sel (Rest ⊕ κ) Rest D v
    (OriginalSourceCoefficientCoordinates.torusMap R κ n J B v hD
      (ExplicitStratumCoordinates.original R κ n (J.erase v.val) B (Sum.inl v.val)))=_
  rw [ExplicitStratumCoordinates.original,OriginalSourceTorusGenerators.parameter,ActualLaurentSheafBaseChange.torusFace_eq,
    LaurentSheafBaseChange.map_parameter]
  rfl

theorem outside (k : Rest ⊕ κ) : map R κ n J B v hD
    (ExplicitStratumCoordinates.original R κ n (J.erase v.val) B ((originals κ n J).symm (Sum.inr k)))=
      algebraMap New (LaurentBasepoint.Laurent New)
        (Ideal.Quotient.mk (ExchangeTransverseSlice.fiberIdeal χ)
          (OriginalTorus.torusCoordinate R (Rest ⊕ κ) k)) := by
  change ActualTorusFace.torusFace R Sel (Rest ⊕ κ) Rest D v
    (OriginalSourceCoefficientCoordinates.torusMap R κ n J B v hD
      (ExplicitStratumCoordinates.original R κ n (J.erase v.val) B ((originals κ n J).symm (Sum.inr k))))=_
  rw [ExplicitStratumCoordinates.original,OriginalSourceTorusGenerators.outside]
  change LocalTransverseTorusFace.torusFace χ v
    (algebraMap (ActualOpenChart.Coefficients R (Rest ⊕ κ)) _
      (OriginalTorus.torusCoordinate R (Rest ⊕ κ) k))=
    algebraMap (ActualOpenChart.Coefficients R (Rest ⊕ κ)) _
      (OriginalTorus.torusCoordinate R (Rest ⊕ κ) k)
  exact AlgHom.commutes _ _

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hJ : Independent (laterWeights κ n B) J)

theorem outside_projection (k : Rest ⊕ κ) : map R κ n J B v hD
    (ExplicitStratumCoordinates.original R κ n (J.erase v.val) B ((originals κ n J).symm (Sum.inr k)))=
      algebraMap New (LaurentBasepoint.Laurent New)
        (OriginalCanonicalFiberProjection.projection R κ n J B hpos hneg hsupport hJ
          (ExplicitStratumCoordinates.original R κ n J B ((originals κ n J).symm (Sum.inr k)))) := by
  rw [outside,OriginalCanonicalFiberGenerators.outside]


theorem remaining (a : AnticliqueSubcolumns.Rows (C := κ) J) : map R κ n J B v hD
    (ExplicitStratumCoordinates.original R κ n (J.erase v.val) B a.val)=
      algebraMap New (LaurentBasepoint.Laurent New)
        (OriginalCanonicalFiberProjection.projection R κ n J B hpos hneg hsupport hJ
          (ExplicitStratumCoordinates.original R κ n J B a.val)) := by
  have ha : (originals κ n J).symm (Sum.inr (GlobalSelectedColumns.rowEquiv κ n J a))=a.val := by
    apply (originals κ n J).injective
    rw [Equiv.apply_symm_apply,ExplicitStratumCoordinates.row_originals]
  simpa only [ha] using outside_projection R κ n J B v hD hpos hneg hsupport hJ
    (GlobalSelectedColumns.rowEquiv κ n J a)

#print axioms map
#print axioms parameter
#print axioms outside
#print axioms outside_projection
#print axioms remaining
end Verification.OriginalSourceLaurentGenerators
