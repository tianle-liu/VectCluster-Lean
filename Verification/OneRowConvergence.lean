/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OneRowSequence
import Verification.SingleGradedFiltration
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# One Row Convergence

Apply one-row degeneration to the actual finite filtration on the
abutment supplied by the standard support spectral sequence.
-/
noncomputable section
namespace Verification.OneRowConvergence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S : OneRowSequence.Pages C) (H : ℕ → C)

structure Input where
  page : ℕ
  filtration : ℕ → SingleGradedFiltration.Data C
  initial : ∀ q,(filtration q).F 0 ≅ H q
  graded : ∀ q p,(filtration q).G p ≅ S.E (page+2) p ((q:ℤ)-p)
  separated : ∀ q,∃ m,IsZero ((filtration q).F (q+1+m))

variable {S H} (D : Input S H)
variable (hrow : ∀ p q,q≠0 → IsZero (S.E 1 p q))

include hrow in
theorem graded_off (q p : ℕ) (hp : p≠q) : IsZero ((D.filtration q).G p) :=
  IsZero.of_iso (OneRowSequence.off_row_of_one_le S hrow (D.page+2) (by omega)
    p ((q:ℤ)-p) (by omega)) (D.graded q p)

def abutmentIso (q : ℕ) : H q ≅ S.E 2 q 0 :=
  (D.initial q).symm ≪≫
    SingleGradedFiltration.singleIso (D.filtration q) q (D.separated q).choose
      (D.separated q).choose_spec (graded_off D hrow q) ≪≫
        (by simpa only [sub_self] using D.graded q q) ≪≫
          OneRowSequence.rowStable S hrow D.page q

def cohomologyIso (K : CochainComplex C ℕ)
    (firstRow : ∀ q,K.homology q ≅ S.E 2 q 0) (q : ℕ) : H q ≅ K.homology q :=
  abutmentIso D hrow q ≪≫ (firstRow q).symm

#print axioms Input
#print axioms graded_off
#print axioms abutmentIso
#print axioms cohomologyIso
end Verification.OneRowConvergence
