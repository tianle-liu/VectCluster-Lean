/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AdjacentStratumLocalization
import Verification.ActualFlagSmoothTame
import Verification.OriginalRostSupport

/-!
# Original Rost Boundary Charts

The ordinary locality theorem now applies to the original exchange
support row with constructed A-algebra coordinates and proved tame smooth
faces. The row is the same row used in OriginalChowIncoming.
-/
noncomputable section
namespace Verification.OriginalRostBoundaryCharts
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
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

def globalSmooth : Algebra.Smooth R A :=
  GlobalExchangeSmooth.global_smooth_tame R κ n B hpos hneg hsupport hf htame

def filtration : RostSupportDivisorInput.Filtration A (Fin n) xs Allowed where
  cover := PrimeCoordinateFiltration.actual_zeroSet_independent R κ n B hpos hneg hsupport
  regular := fun I hI => OriginalGZeroGeometry.local_regular R κ n B hpos hneg hsupport I hI (hf I hI)

variable (T : RostAffineInput.Theory) (S : RostSupportInput.Theory T)
variable (P : RostPrincipalLocalizationInput.Theory T)

theorem row_eq_support (s : ℤ) :
    letI := globalSmooth R κ n B hpos hneg hsupport hf htame
    RostSupportDivisorInput.row T S A (Fin n) xs Allowed R
      (filtration R κ n B hpos hneg hsupport hf) s =
        OriginalRostSupport.support T S R κ n B hpos hneg hsupport hf htame s := rfl

variable (J : Finset (Fin n)) (hJ : Independent (laterWeights κ n B) J) (v : J)

include hpos hneg hsupport hf htame hJ in
theorem face_smooth : Algebra.Smooth R (RostSupportDivisorInput.Face A (Fin n) xs J v) := by
  obtain ⟨m, sm, he⟩ := htame J hJ
  exact ActualFlagSmoothTame.old_smooth R κ n J B v
    (matrix_zero_block κ n J B hpos hneg hsupport hJ) (hf J hJ) sm he

include hpos hneg hsupport hf hJ in
theorem face_regular : IsRegular (RostSupportDivisorInput.parameter A (Fin n) xs J v) := by
  have h : IsLeftRegular (RostSupportDivisorInput.parameter A (Fin n) xs J v) :=
    ActualFlagRegular.parameter_regular R κ n J B v
      (matrix_zero_block κ n J B hpos hneg hsupport hJ) (hf J hJ)
  exact ⟨h, h.right_of_commute (fun b => mul_comm _ b)⟩

def coordinates : RostSupportDivisorInput.Coordinates A (Fin n) xs (J.erase v.val) J v :=
  AdjacentStratumLocalization.coordinates A (Fin n) xs J v

def Standard : Prop := by
  letI := globalSmooth R κ n B hpos hneg hsupport hf htame
  exact RostSupportDivisorInput.Standard T S P A (Fin n) xs Allowed R
    (filtration R κ n B hpos hneg hsupport hf)

variable (C : Standard R κ n B hpos hneg hsupport hf htame T S P)

include hpos hneg hsupport hf htame C in
theorem nonincident (s : ℤ) (p : ℕ) (I : PrimeLayerCover.Index Allowed p)
    (J : PrimeLayerCover.Index Allowed (p+1)) (h : ¬ I.val ⊆ J.val) :
    RostSupportRowBlocks.block T A (Fin n) xs Allowed s
      (OriginalRostSupport.support T S R κ n B hpos hneg hsupport hf htame s) p I J = 0 := by
  letI := globalSmooth R κ n B hpos hneg hsupport hf htame
  exact C.nonincident s p I J h

include hpos hneg hsupport hf htame C in
theorem adjacent (s : ℤ) (p : ℕ) (I : PrimeLayerCover.Index Allowed p)
    (J : PrimeLayerCover.Index Allowed (p+1)) (v : J.val)
    (h : I.val = J.val.erase v.val) :
    letI := globalSmooth R κ n B hpos hneg hsupport hf htame
    letI := face_smooth R κ n B hpos hneg hsupport hf htame J.val J.property.2 v
    let e : RostSupportDivisorInput.Coordinates A (Fin n) xs I.val J.val v :=
      h ▸ coordinates R κ n B J.val v
    RostSupportRowBlocks.block T A (Fin n) xs Allowed s
      (OriginalRostSupport.support T S R κ n B hpos hneg hsupport hf htame s) p I J =
        RostSupportDivisorInput.localBoundary T P A (Fin n) xs Allowed R s p I J v
          (face_regular R κ n B hpos hneg hsupport hf J.val J.property.2 v) e := by
  letI := globalSmooth R κ n B hpos hneg hsupport hf htame
  letI := face_smooth R κ n B hpos hneg hsupport hf htame J.val J.property.2 v
  exact C.adjacent s p I J v h _ _

#print axioms globalSmooth
#print axioms filtration
#print axioms row_eq_support
#print axioms face_smooth
#print axioms face_regular
#print axioms coordinates
#print axioms Standard
#print axioms nonincident
#print axioms adjacent
end Verification.OriginalRostBoundaryCharts
