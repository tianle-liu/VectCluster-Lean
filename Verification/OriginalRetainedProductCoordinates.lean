/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalRemainingCoordinates
import Verification.OriginalRemainingComponents
import Verification.AffineTorusCoefficientProduct
import Verification.ProductComponentIdempotents

/-!
# Original Retained Product Coordinates

A chosen product decomposition of the retained coefficient ring is
extended functorially to the original stratum. Original free coordinates
and coefficient idempotents are both tracked through the same ring map.
-/
noncomputable section
namespace Verification.OriginalRetainedProductCoordinates
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open Verification.IndependentChartIndex Verification.OriginalFreeTorusCoordinates
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

structure ProductData where
  Index : Type
  finiteIndex : Fintype Index
  Factor : Index → Type
  factorRing : ∀ j, CommRing (Factor j)
  factorAlgebra : ∀ j, Algebra R (Factor j)
  factorDomain : ∀ j, IsDomain (Factor j)
  equiv : RemainingRing R κ n I B ≃ₐ[R] ∀ j, Factor j

attribute [instance] ProductData.finiteIndex ProductData.factorRing
  ProductData.factorAlgebra ProductData.factorDomain

def decomposition (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
    {m : ℕ} (s : Basis.SmithNormalForm
      (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)) (Other n I ⊕ κ) m)
    (he : ∀ i, IsUnit ((s.a i).natAbs : R)) : ProductData R κ n I B :=
  Classical.choice (by
    obtain ⟨J, hJ, L, hL, aL, K, hK, E, _⟩ :=
      OriginalRemainingComponents.separable_product R κ n I B hf s he
    letI := hJ
    letI := hL
    letI := aL
    letI := hK
    exact ⟨{
      Index := J
      finiteIndex := Fintype.ofFinite J
      Factor := fun j => OriginalTorus.Torus (L j) K
      factorRing := fun _ => inferInstance
      factorAlgebra := fun _ => inferInstance
      factorDomain := fun _ => inferInstance
      equiv := E }⟩)

variable (D : ProductData R κ n I B)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, FrozenAcyclicCover.earlierWeights κ n B i j = 0 ↔
  FrozenAcyclicCover.laterWeights κ n B i j = 0)
variable (hI : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) I)

def stratumEquiv : GlobalNormalFrame.ZeroLayer R κ n I B ≃ₐ[R]
    ∀ j, MvPolynomial (Selected n I) (OriginalTorus.Torus (D.Factor j) (FreeIndex κ n I B)) :=
  (OriginalFreeTorusCoordinates.stratumEquiv R κ n I B hpos hneg hsupport hI).trans
    (AffineTorusCoefficientProduct.affineEquiv D.Factor D.equiv (Selected n I) (FreeIndex κ n I B))

theorem coefficient (a : RemainingRing R κ n I B) (j : D.Index) :
    stratumEquiv R κ n I B D hpos hneg hsupport hI
      (OriginalRemainingCoordinates.inclusion R κ n I B hpos hneg hsupport hI a) j =
      MvPolynomial.C (algebraMap (D.Factor j)
        (OriginalTorus.Torus (D.Factor j) (FreeIndex κ n I B)) (D.equiv a j)) := by
  change AffineTorusCoefficientProduct.affineEquiv D.Factor D.equiv (Selected n I) (FreeIndex κ n I B)
    (OriginalFreeTorusCoordinates.stratumEquiv R κ n I B hpos hneg hsupport hI
      ((OriginalFreeTorusCoordinates.stratumEquiv R κ n I B hpos hneg hsupport hI).symm _)) j = _
  rw [AlgEquiv.apply_symm_apply]
  exact AffineTorusCoefficientProduct.coefficient D.Factor D.equiv (Selected n I) (FreeIndex κ n I B) a j

theorem original_variable (k : FreeIndex κ n I B) (j : D.Index) :
    stratumEquiv R κ n I B D hpos hneg hsupport hI
      (ExplicitStratumCoordinates.original R κ n I B
        ((GlobalSelectedColumns.rowEquiv κ n I).symm k.val).val) j =
      MvPolynomial.C (OriginalTorus.torusCoordinate (D.Factor j) (FreeIndex κ n I B) k) := by
  change AffineTorusCoefficientProduct.affineEquiv D.Factor D.equiv (Selected n I) (FreeIndex κ n I B)
    (OriginalFreeTorusCoordinates.stratumEquiv R κ n I B hpos hneg hsupport hI _) j = _
  rw [OriginalFreeCoordinateGraph.stratum_original_coordinate]
  exact AffineTorusCoefficientProduct.torus_variable D.Factor D.equiv (Selected n I) (FreeIndex κ n I B) k j

theorem inclusion_indicator (j : D.Index) :
    OriginalRemainingCoordinates.inclusion R κ n I B hpos hneg hsupport hI
      (ProductComponentIdempotents.indicator D.Factor D.equiv.toRingEquiv j) =
    ProductComponentIdempotents.indicator
      (fun j => MvPolynomial (Selected n I) (OriginalTorus.Torus (D.Factor j) (FreeIndex κ n I B)))
      (stratumEquiv R κ n I B D hpos hneg hsupport hI).toRingEquiv j := by
  classical
  apply (stratumEquiv R κ n I B D hpos hneg hsupport hI).injective
  change _ = (stratumEquiv R κ n I B D hpos hneg hsupport hI).toRingEquiv _
  rw [ProductComponentIdempotents.image_indicator]
  funext l
  rw [coefficient]
  have h : D.equiv (ProductComponentIdempotents.indicator D.Factor D.equiv.toRingEquiv j) =
      Pi.single j 1 := ProductComponentIdempotents.image_indicator D.Factor D.equiv.toRingEquiv j
  rw [h]
  by_cases hl : l = j
  · subst l
    simp only [Pi.single_eq_same, map_one]
  · simp [Pi.single_apply, hl]

#print axioms ProductData
#print axioms decomposition
#print axioms stratumEquiv
#print axioms coefficient
#print axioms original_variable
#print axioms inclusion_indicator
end Verification.OriginalRetainedProductCoordinates
