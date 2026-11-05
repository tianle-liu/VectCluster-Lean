/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalFreeCoordinateGraph
import Verification.FreeCharacterRemainingCoordinates

/-!
# Original Remaining Coordinates

The complementary coefficient algebra in the A(I)-preserving torus
splitting is embedded into the literal stratum. Its generators remain
the original mutable/frozen coordinates, rather than new Smith variables.
-/
noncomputable section
namespace Verification.OriginalRemainingCoordinates
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 300000
open Verification.IndependentChartIndex Verification.OriginalFreeTorusCoordinates
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

omit [Fintype κ] in
theorem splitting_remaining (j : RemainingIndex κ n I B) :
    splitting κ n I B (Finsupp.single j.val 1) = (0, Finsupp.single j 1) := by
  classical
  apply Prod.ext
  · ext k
    change (Finsupp.single j.val (1 : ℤ)) k.val = 0
    apply Finsupp.single_eq_of_ne
    intro h
    exact j.property (h.symm ▸ k.property)
  · ext k
    change (Finsupp.single j.val (1 : ℤ)) k.val = (Finsupp.single j 1) k
    by_cases h : j = k
    · subst k
      simp
    · simp [Finsupp.single_eq_of_ne (fun he => h (Subtype.ext he)),
        Finsupp.single_eq_of_ne h]

#print axioms splitting_remaining

theorem fiber_remaining (j : RemainingIndex κ n I B) :
    fiberEquiv R κ n I B (Ideal.Quotient.mk _
      (OriginalTorus.torusCoordinate R (Other n I ⊕ κ) j.val)) =
        algebraMap (RemainingRing R κ n I B)
          (OriginalTorus.Torus (RemainingRing R κ n I B) (FreeIndex κ n I B))
          (Ideal.Quotient.mk (remainingIdeal R κ n I B)
            (OriginalTorus.torusCoordinate R (RemainingIndex κ n I B) j)) :=
  FreeCharacterRemainingCoordinates.remaining_of_image R ((Other n I ⊕ κ) →₀ ℤ)
    (FreeIndex κ n I B →₀ ℤ) (RemainingIndex κ n I B →₀ ℤ) (Selected n I)
    (splitting κ n I B)
    (ActualOpenChart.column (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B))
    (fun _ => -1) (columns_free_zero κ n I B) _ (fiberIdeal_eq R κ n I B)
    (Finsupp.single j.val 1) (Finsupp.single j 1) (splitting_remaining κ n I B j)

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, FrozenAcyclicCover.earlierWeights κ n B i j = 0 ↔
  FrozenAcyclicCover.laterWeights κ n B i j = 0)
variable (hI : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) I)

theorem stratum_remaining (j : RemainingIndex κ n I B) :
    stratumEquiv R κ n I B hpos hneg hsupport hI
      (ExplicitStratumCoordinates.original R κ n I B
        ((GlobalSelectedColumns.rowEquiv κ n I).symm j.val).val) =
      algebraMap (RemainingRing R κ n I B)
        (MvPolynomial (Selected n I)
          (OriginalTorus.Torus (RemainingRing R κ n I B) (FreeIndex κ n I B)))
        (Ideal.Quotient.mk (remainingIdeal R κ n I B)
          (OriginalTorus.torusCoordinate R (RemainingIndex κ n I B) j)) := by
  dsimp only [stratumEquiv, AlgEquiv.trans_apply]
  rw [ExplicitStratumCoordinates.affineEquiv_original,
    MvPolynomial.mapAlgEquiv_apply, MvPolynomial.map_C]
  change MvPolynomial.C (fiberEquiv R κ n I B
    (Ideal.Quotient.mk _ (OriginalTorus.torusCoordinate R (Other n I ⊕ κ)
      (GlobalSelectedColumns.rowEquiv κ n I ((GlobalSelectedColumns.rowEquiv κ n I).symm j.val))))) = _
  rw [Equiv.apply_symm_apply, fiber_remaining]
  rfl

def inclusion : RemainingRing R κ n I B →ₐ[R] GlobalNormalFrame.ZeroLayer R κ n I B :=
  (stratumEquiv R κ n I B hpos hneg hsupport hI).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom R (RemainingRing R κ n I B)
      (MvPolynomial (Selected n I)
        (OriginalTorus.Torus (RemainingRing R κ n I B) (FreeIndex κ n I B))))

theorem inclusion_generator (j : RemainingIndex κ n I B) :
    inclusion R κ n I B hpos hneg hsupport hI
      (Ideal.Quotient.mk (remainingIdeal R κ n I B)
        (OriginalTorus.torusCoordinate R (RemainingIndex κ n I B) j)) =
      ExplicitStratumCoordinates.original R κ n I B
        ((GlobalSelectedColumns.rowEquiv κ n I).symm j.val).val := by
  apply (stratumEquiv R κ n I B hpos hneg hsupport hI).injective
  change stratumEquiv R κ n I B hpos hneg hsupport hI
    ((stratumEquiv R κ n I B hpos hneg hsupport hI).symm _) = _
  rw [AlgEquiv.apply_symm_apply, stratum_remaining]
  rfl


#print axioms fiber_remaining
#print axioms stratum_remaining
#print axioms inclusion
#print axioms inclusion_generator
end Verification.OriginalRemainingCoordinates
