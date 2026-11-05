/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Homology

/-!
# One Row Sequence

The one-row degeneration argument on actual categorical homology.
The page and convergence data are inputs from the standard support spectral
sequence; no vanishing or collapse of the manuscript is an input.
-/
noncomputable section
namespace Verification.OneRowSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable (C : Type u) [Category.{v} C] [Abelian C]

structure Pages where
  E : ℕ → ℤ → ℤ → C
  differential : ℕ → ℤ → ℤ → ShortComplex C
  source : ∀ r p q,(differential r p q).X₁ ≅ E r (p-r) (q+r-1)
  middle : ∀ r p q,(differential r p q).X₂ ≅ E r p q
  target : ∀ r p q,(differential r p q).X₃ ≅ E r (p+r) (q-r+1)
  next : ∀ r p q,(differential r p q).homology ≅ E (r+1) p q

variable {C} (S : Pages C)
variable (hrow : ∀ p q,q≠0 → IsZero (S.E 1 p q))

include hrow in
theorem off_row (n : ℕ) (p q : ℤ) (hq : q≠0) : IsZero (S.E (n+1) p q) := by
  induction n with
  | zero => exact hrow p q hq
  | succ n ih =>
    exact IsZero.of_iso ((S.differential (n+1) p q).isZero_homology_of_isZero_X₂
      (IsZero.of_iso ih (S.middle (n+1) p q))) (S.next (n+1) p q).symm

include hrow in
theorem off_row_of_one_le (r : ℕ) (hr : 1≤r) (p q : ℤ) (hq : q≠0) : IsZero (S.E r p q) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hr
  simpa only [Nat.add_comm 1 n] using off_row S hrow n p q hq

include hrow in
theorem incoming_zero (r : ℕ) (hr : 2≤r) (p : ℤ) : (S.differential r p 0).f=0 := by
  have hz := IsZero.of_iso (off_row_of_one_le S hrow r (by omega) (p-r) (0+r-1) (by omega))
    (S.source r p 0)
  exact hz.eq_of_src _ _

include hrow in
theorem outgoing_zero (r : ℕ) (hr : 2≤r) (p : ℤ) : (S.differential r p 0).g=0 := by
  have hz := IsZero.of_iso (off_row_of_one_le S hrow r (by omega) (p+r) (0-r+1) (by omega))
    (S.target r p 0)
  exact hz.eq_of_tgt _ _

def rowStep (r : ℕ) (hr : 2≤r) (p : ℤ) : S.E (r+1) p 0 ≅ S.E r p 0 :=
  (S.next r p 0).symm ≪≫
    (ShortComplex.HomologyData.ofZeros (S.differential r p 0)
      (incoming_zero S hrow r hr p) (outgoing_zero S hrow r hr p)).left.homologyIso ≪≫
        S.middle r p 0

def rowStable (n : ℕ) (p : ℤ) : S.E (n+2) p 0 ≅ S.E 2 p 0 := by
  induction n with
  | zero => exact Iso.refl _
  | succ n ih => exact rowStep S hrow (n+2) (by omega) p ≪≫ ih

#print axioms Pages
#print axioms off_row
#print axioms off_row_of_one_le
#print axioms incoming_zero
#print axioms outgoing_zero
#print axioms rowStep
#print axioms rowStable
end Verification.OneRowSequence
