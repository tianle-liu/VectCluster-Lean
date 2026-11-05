/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IndependentStratumCoordinates
import Verification.ActualCoordinateFlag
import Verification.CoordinateFlagTotalQuotient
import Verification.ActualTransverseZeroSection

/-!
# Original Canonical Fiber Projection

The torus-fiber projection of an actual stratum is independent of
which adjacent flag is used. All maps retain the literal original
quotient coordinates; the projection sets the affine partners to zero.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalCanonicalFiberProjection
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.IndependentBasicOpen Verification.IndependentOpenCoordinates
open Verification.ExchangeOpenCover
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (v : Selected n I)
local notation "A" => BasicOpen R κ n I B
local notation "Sel" => Selected n I
local notation "Rest" => Other n I
local notation "D" => matrix κ n I B
local notation "x" => selectedCoordinate R κ n I B
local notation "All" => CoordinateFlag.ClosedAll A Sel x v
local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R Sel (Rest ⊕ κ) Rest D)

theorem full_square :
    (ActualTransverseClosed.closedToFull R Sel (Rest ⊕ κ) Rest Sum.inl D v).toAlgHom.comp
      (ActualCoordinateFlag.closedEquiv R κ n I B v).toAlgHom =
    (IndependentStratumCoordinates.quotientChart R κ n I B).toAlgHom.comp
      (CoordinateFlagTotalQuotient.equiv R A Sel x v).toAlgHom := by
  apply AlgHom.ext
  intro a
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  change ActualTransverseClosed.closedToFull R Sel (Rest ⊕ κ) Rest Sum.inl D v
      (ActualCoordinateFlag.closedEquiv R κ n I B v
        (Ideal.Quotient.mk (CoordinateFlag.finalIdeal A Sel x v)
          (Ideal.Quotient.mk (CoordinateFlag.oldIdeal A Sel x v) a))) =
    IndependentStratumCoordinates.quotientChart R κ n I B
      (CoordinateFlagTotalQuotient.equiv R A Sel x v
        (Ideal.Quotient.mk (CoordinateFlag.finalIdeal A Sel x v)
          (Ideal.Quotient.mk (CoordinateFlag.oldIdeal A Sel x v) a)))
  rw [ActualCoordinateFlag.closedEquiv_mk, ActualCoordinateFlag.intermediateEquiv_mk,
    ActualTransverseClosed.closedToFull_mk, CoordinateFlagTotalQuotient.equiv_mk]
  rfl


variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hI : Independent (laterWeights κ n B) I)
local notation "hD" => matrix_zero_block κ n I B hpos hneg hsupport hI

def projection : GlobalNormalFrame.ZeroLayer R κ n I B →ₐ[R] New :=
  (PolynomialSectionIso.zeroEvaluation R New Sel).comp
    (IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI).toAlgHom

theorem affine_square :
    (ActualTransverseClosed.affineEquiv R Sel (Rest ⊕ κ) Rest Sum.inl D v hD).toAlgHom.comp
      (ActualCoordinateFlag.closedEquiv R κ n I B v).toAlgHom =
    (IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI).toAlgHom.comp
      (CoordinateFlagTotalQuotient.equiv R A Sel x v).toAlgHom := by
  have h := full_square R κ n I B v
  apply AlgHom.ext
  intro a
  exact congrArg
    ((ExchangeZeroFiber.affineEquiv (R := R) (ActualOpenChart.characters R Sel (Rest ⊕ κ) Rest D)).toAlgHom.comp
      (ActualTransverseClosed.fullToLocal R Sel (Rest ⊕ κ) Rest Sum.inl D hD).toAlgHom)
    (AlgHom.congr_fun h a)

theorem projection_square :
    (ActualTransverseLocalization.closedSlice R Sel (Rest ⊕ κ) Rest Sum.inl D hD v).comp
      (ActualCoordinateFlag.closedEquiv R κ n I B v).toAlgHom =
    (projection R κ n I B hpos hneg hsupport hI).comp
      (CoordinateFlagTotalQuotient.equiv R A Sel x v).toAlgHom := by
  rw [ActualTransverseZeroSection.closedSlice_zeroSection]
  rw [AlgHom.comp_assoc, affine_square R κ n I B v hpos hneg hsupport hI]
  rfl

theorem projection_factorization : projection R κ n I B hpos hneg hsupport hI =
    (ActualTransverseLocalization.closedSlice R Sel (Rest ⊕ κ) Rest Sum.inl D hD v).comp
      ((ActualCoordinateFlag.closedEquiv R κ n I B v).toAlgHom.comp
        (CoordinateFlagTotalQuotient.equiv R A Sel x v).symm.toAlgHom) := by
  apply AlgHom.ext
  intro a
  have h := AlgHom.congr_fun (projection_square R κ n I B v hpos hneg hsupport hI)
    ((CoordinateFlagTotalQuotient.equiv R A Sel x v).symm a)
  change ActualTransverseLocalization.closedSlice R Sel (Rest ⊕ κ) Rest Sum.inl D hD v
      (ActualCoordinateFlag.closedEquiv R κ n I B v
        ((CoordinateFlagTotalQuotient.equiv R A Sel x v).symm a)) =
    projection R κ n I B hpos hneg hsupport hI
      ((CoordinateFlagTotalQuotient.equiv R A Sel x v)
        ((CoordinateFlagTotalQuotient.equiv R A Sel x v).symm a)) at h
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm


#print axioms full_square
#print axioms projection
#print axioms affine_square
#print axioms projection_square
#print axioms projection_factorization
end Verification.OriginalCanonicalFiberProjection
