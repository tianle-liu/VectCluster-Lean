/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostSupportInput
import Verification.OriginalRostStrata
import Verification.OriginalGZeroGeometry

/-!
# Original Rost Support

Instantiate the ordinary support sequence on the manuscript's
literal coordinate filtration. Tame Smith factors imply stratum
acyclicity; one-row degeneration and removal of all extension ambiguity
are internal deductions. The remaining row differential is not assumed
to have the article's component-cokernel formula.
-/
noncomputable section
namespace Verification.OriginalRostSupport
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

def support (s : ℤ) : RostSupportInput.Data T (Global R κ n B) (Fin n)
    (fun i => initial R κ n B (Sum.inl i)) (Independent (laterWeights κ n B)) s := by
  letI := GlobalExchangeSmooth.global_smooth_tame R κ n B hpos hneg hsupport hf htame
  exact S.sequence R (Global R κ n B) (Fin n)
    (fun i => initial R κ n B (Sum.inl i)) (Independent (laterWeights κ n B))
    (PrimeCoordinateFiltration.actual_zeroSet_independent R κ n B hpos hneg hsupport)
    (fun I hI => OriginalGZeroGeometry.local_regular R κ n B hpos hneg hsupport I hI (hf I hI)) s

include F hpos hneg hsupport hf htame in
theorem layer_positive (s : ℤ) (p q : ℕ) (hq : 0<q) :
    IsZero (RostSupportInput.Layer T (Global R κ n B) (Fin n)
      (fun i => initial R κ n B (Sum.inl i)) (Independent (laterWeights κ n B)) s p q) := by
  have hz (I : PrimeLayerCover.Index (Independent (laterWeights κ n B)) p) :
      IsZero ((T.cycles (Spec (CommRingCat.of (PrimeStratumPresentation.ClosedRing
        (fun i => initial R κ n B (Sum.inl i)) I.val))) (s-p)).homology q) := by
    obtain ⟨m,sm,he⟩ := htame I.val I.property.2
    exact OriginalRostStrata.positive T F R κ n B hpos hneg hsupport I.val I.property.2
      (hf I.val I.property.2) sm he (s-p) q hq
  letI : Subsingleton (RostSupportInput.Layer T (Global R κ n B) (Fin n)
      (fun i => initial R κ n B (Sum.inl i)) (Independent (laterWeights κ n B)) s p q) :=
    ⟨fun a b => by
      funext I
      exact congrArg (fun f => f (a I)) ((hz I).eq_of_src (𝟙 _) 0) |>.trans
        (congrArg (fun f => f (b I)) ((hz I).eq_of_src (𝟙 _) 0)).symm⟩
  exact AddCommGrp.isZero_of_subsingleton _

variable (s : ℤ)
local notation "D" => support T S R κ n B hpos hneg hsupport hf htame s

include F in
theorem one_row (p q : ℤ) (hq : q≠0) : IsZero ((D).pages.E 1 p q) := by
  by_cases hp : p<0
  · exact (D).negative_p p q hp
  by_cases hn : q<0
  · exact (D).negative_q p q hn
  lift p to ℕ using le_of_not_gt hp
  lift q to ℕ using le_of_not_gt hn
  exact IsZero.of_iso (layer_positive T F R κ n B hpos hneg hsupport hf htame s p q (by omega))
    ((D).first p q)

def cohomologyIso (q : ℕ) :
    (T.cycles (Spec (CommRingCat.of (Global R κ n B))) s).homology q ≅ (D).row.homology q :=
  OneRowConvergence.cohomologyIso (D).convergence
    (one_row T F S R κ n B hpos hneg hsupport hf htame s) (D).row (D).rowHomology q

#print axioms support
#print axioms layer_positive
#print axioms one_row
#print axioms cohomologyIso
end Verification.OriginalRostSupport
