/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalKZero
import Verification.OriginalBundleRange
import Verification.StableOrientations

/-!
# Original Line Bundles

The original exchange scheme has only the trivial line-bundle
isomorphism class under AS. Global stable freeness is already derived
from its actual G_0 filtration, and rank-one cancellation follows from
the ordinary determinant identities, without a Picard-vanishing premise.
-/
noncomputable section
namespace Verification.OriginalLineBundles
open CategoryTheory AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hf : ∀ I,Independent (laterWeights κ n B) I → Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I,Independent (laterWeights κ n B) I → FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable {G : Scheme → Type*} [∀ X,AddCommGroup (G X)]
variable (T : SchemeGZeroInput.Theory G) (K : SchemeGZeroInput.Koszul T)
variable (ST : SchemeGZeroInput.SplitAffineTorus T) (L : SchemeGZeroInput.Localization T)
variable (SC : SmoothCartanInput.Standard)


def domain : IsDomain (Global R κ n B) :=
  OriginalBundleRange.originalDomain R κ n B hpos hneg hsupport hf hs

variable (Det : DeterminantStandardInput.Standard (Global R κ n B))
variable (F : Type) [Field F] [Algebra (Global R κ n B) F]

include hpos hneg hsupport hf hs T K ST L SC F Det in
theorem line_free (Q : ActualProjectiveSplitting.Bundle (Global R κ n B))
    (hq : ActualProjectiveSplitting.HasRank Q 1) : ActualProjectiveSplitting.Trivial Q := by
  letI := domain R κ n B hpos hneg hsupport hf hs
  exact StableOrientations.line_free Det Q hq
    (OriginalKZero.stably_free R κ n B hpos hneg hsupport hf hs T K ST L SC F Q)

include hpos hneg hsupport hf hs T K ST L SC F Det in
theorem classes_subsingleton :
    letI := domain R κ n B hpos hneg hsupport hf hs;
    Subsingleton (RankedProjectiveClasses.Classes (Global R κ n B) 1) := by
  letI := domain R κ n B hpos hneg hsupport hf hs
  have h (x : RankedProjectiveClasses.Classes (Global R κ n B) 1) :
      x=RankedProjectiveClasses.trivial (Global R κ n B) 1 := by
    induction x using Quotient.inductionOn with
    | h Q =>
      exact (RankedProjectiveClasses.eq_trivial (Global R κ n B) Q.val Q.property).mpr
        (line_free R κ n B hpos hneg hsupport hf hs T K ST L SC Det F Q.val Q.property)
  exact ⟨fun x y => (h x).trans (h y).symm⟩

#print axioms domain
#print axioms line_free
#print axioms classes_subsingleton
end Verification.OriginalLineBundles
