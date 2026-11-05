/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.NisnevichSplittingInput

/-!
# Nisnevich Bundle Splitting

Repeated splitting on an actual smooth affine domain, with the
rank-zero base case and constant-rank existence proved internally.
-/
namespace Verification.NisnevichBundleSplitting
open Verification.ActualProjectiveSplitting
universe u
variable {M : Type u} (T : StrictNisnevichInput.Theory M)
variable (k : Type) [Field k] (S : NisnevichSplittingInput.Standard T k)
variable (A : Type) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.Smooth k A]
include S k in
theorem all_free (hb : StrictCohomologicalDimension.Bound T A 1)
    (hl : ∀ P : Bundle A, HasRank P 1 → Trivial P) (P : Bundle A) : Trivial P := by
  apply ProjectiveConstantRank.all_free hl _ P
  intro r Q hQ
  exact S.split A 1 hb (r+1) (by omega) Q hQ

#print axioms all_free
end Verification.NisnevichBundleSplitting
