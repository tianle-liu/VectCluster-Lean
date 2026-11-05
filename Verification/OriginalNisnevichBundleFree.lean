/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalLineBundles
import Verification.OriginalFramedNisnevich
import Verification.NisnevichBundleSplitting

/-!
# Original Nisnevich Bundle Free

Every actual finite projective module is free once the original seed
has strict cohomological dimension at most one. Picard vanishing and
constant rank are already proved, and only the cited single-line
splitting theorem is used here.
-/
noncomputable section
namespace Verification.OriginalNisnevichBundleFree
open CategoryTheory AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.ActualProjectiveSplitting
universe u
variable {M : Type u} (N : StrictNisnevichInput.Theory M)
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (S : NisnevichSplittingInput.Standard N R)
variable (B : (Fin n⊕κ) → (Fin n⊕Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hf : ∀ I,Independent (laterWeights κ n B) I → Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I,Independent (laterWeights κ n B) I → FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable {G : Scheme → Type*} [∀ X,AddCommGroup (G X)]
variable (T : SchemeGZeroInput.Theory G) (K : SchemeGZeroInput.Koszul T)
variable (ST : SchemeGZeroInput.SplitAffineTorus T) (L : SchemeGZeroInput.Localization T)
variable (SC : SmoothCartanInput.Standard)
variable (Det : DeterminantStandardInput.Standard (Global R κ n B))
variable (F : Type) [Field F] [Algebra (Global R κ n B) F]
include hpos hneg hsupport hf hs T K ST L SC F Det S in
theorem all_free (hb : StrictCohomologicalDimension.Bound N (Global R κ n B) 1)
    (Q : Bundle (Global R κ n B)) : Trivial Q := by
  letI := OriginalLineBundles.domain R κ n B hpos hneg hsupport hf hs
  letI := GlobalExchangeSmooth.global_smooth_saturated R κ n B hpos hneg hsupport hf hs
  exact NisnevichBundleSplitting.all_free N R S (Global R κ n B) hb
    (OriginalLineBundles.line_free R κ n B hpos hneg hsupport hf hs T K ST L SC Det F) Q

#print axioms all_free
end Verification.OriginalNisnevichBundleFree
