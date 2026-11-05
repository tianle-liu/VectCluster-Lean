/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalRostSupport
import Verification.RostRowTruncation
import Verification.AdditiveTerminalHomology

/-!
# Original Chow Row

The manuscript's Chow groups are the homology of its actual support
row, with the independence-height bound and vanishing last outgoing map.
Only the ordinary uniform diagonal cycle/Chow comparison is external;
the component formula for the incoming differential remains separate.
-/
noncomputable section
namespace Verification.OriginalChowRow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentChartIndex
variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (S : RostSupportInput.Theory T)
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hf : ∀ I,Independent (laterWeights κ n B) I → Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (htame : ∀ I,Independent (laterWeights κ n B) I →
  ∃ (m : ℕ) (sm : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I))
    (Other n I⊕κ) m),∀ i,IsUnit ((sm.a i).natAbs : R))

variable (CH : Scheme → ℕ → AddCommGrp) (K : RostMilnorInput.ChowComparison T CH)

local notation "A" => Global R κ n B
local notation "D" p => OriginalRostSupport.support T S R κ n B hpos hneg hsupport hf htame p

def chowRowIso (p : ℕ) : CH (Spec (CommRingCat.of A)) p ≅ (D p).row.homology p := by
  letI := GlobalExchangeSmooth.global_smooth_tame R κ n B hpos hneg hsupport hf htame
  exact K.diagonal R A p ≪≫
    OriginalRostSupport.cohomologyIso T F S R κ n B hpos hneg hsupport hf htame p p

include F K S hpos hneg hsupport hf htame in
theorem chow_above_height (p : ℕ)
    (hp : PrimeIndependentHeight.height (Fin n) (Independent (laterWeights κ n B)) < p) :
    IsZero (CH (Spec (CommRingCat.of A)) p) :=
  IsZero.of_iso (RostSupportBounds.row_homology_above T A (Fin n)
    (fun i => initial R κ n B (Sum.inl i)) (Independent (laterWeights κ n B)) p (D p) p hp)
      (chowRowIso T F S R κ n B hpos hneg hsupport hf htame CH K p)

theorem last_outgoing_zero (N : RostMilnorInput.NegativeWeights T) (p : ℕ) :
    (D p).row.d p (p+1)=0 :=
  RostRowTruncation.outgoing_zero T N A (Fin n)
    (fun i => initial R κ n B (Sum.inl i)) (Independent (laterWeights κ n B)) p (D p)

def chowQuotientIso (N : RostMilnorInput.NegativeWeights T) (p : ℕ) (hp : 0<p) :
    CH (Spec (CommRingCat.of A)) p ≅
      AddCommGrp.of ((D p).row.X p ⧸ AddMonoidHom.range ((D p).row.d (p-1) p).hom) :=
  chowRowIso T F S R κ n B hpos hneg hsupport hf htame CH K p ≪≫
    AdditiveTerminalHomology.terminalIso (D p).row p hp
      (last_outgoing_zero T S R κ n B hpos hneg hsupport hf htame N p)

#print axioms chowQuotientIso
#print axioms chowRowIso
#print axioms chow_above_height
#print axioms last_outgoing_zero
end Verification.OriginalChowRow
