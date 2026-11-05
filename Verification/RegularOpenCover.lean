/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Regular.SMul

/-!
# Regular Open Cover

Nonzerodivisors are detected on a principal open cover of one fixed
ring. This glues the actual coordinate calculations without assuming the
global ring to be integral.
-/
noncomputable section
namespace Verification.RegularOpenCover
variable {A : Type*} [CommRing A]

theorem of_span (s : Set A) (hs : Ideal.span s = ⊤) (x : A)
    (hx : ∀ r : s, IsSMulRegular (Localization.Away r.val)
      (algebraMap A (Localization.Away r.val) x)) : IsSMulRegular A x := by
  intro a b hab
  apply Localization.algebraMap_injective_of_span_eq_top s hs
  funext r
  apply hx r
  change algebraMap A (Localization.Away r.val) x * algebraMap A (Localization.Away r.val) a =
    algebraMap A (Localization.Away r.val) x * algebraMap A (Localization.Away r.val) b
  rw [← map_mul,← map_mul]
  exact congrArg (algebraMap A (Localization.Away r.val)) hab

theorem of_family {ι : Type*} (r : ι → A) (hs : Ideal.span (Set.range r) = ⊤) (x : A)
    (hx : ∀ i, IsSMulRegular (Localization.Away (r i))
      (algebraMap A (Localization.Away (r i)) x)) : IsSMulRegular A x := by
  apply of_span (Set.range r) hs x
  rintro ⟨a,⟨i,rfl⟩⟩
  exact hx i

#print axioms of_span
#print axioms of_family
end Verification.RegularOpenCover
