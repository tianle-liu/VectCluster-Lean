/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittOutsideBits
import Verification.ExplicitStratumCoordinates

/-!
# Original Witt Original Exponent

The outside-character exponent of an actual original coordinate is
the manuscript's literal standard basis vector in F_2^(n+m).
-/
noncomputable section
open scoped Classical
namespace Verification.OriginalWittOriginalExponent
open Verification.IndependentChartIndex Verification.OriginalWittCharacterSplitting
variable (κ : Type) [Fintype κ] (n : ℕ) (I : Finset (Fin n))

omit [Fintype κ] in
theorem single (a : AnticliqueSubcolumns.Rows (C := κ) I) :
    OriginalWittOutsideBits.exponent κ n I (Finsupp.single (GlobalSelectedColumns.rowEquiv κ n I a) 1) =
      Pi.single a.val (1 : ZMod 2) := by
  apply (splitBits κ n I).injective
  rw [OriginalWittOutsideBits.exponent,LinearEquiv.apply_symm_apply,splitBits_apply]
  apply Prod.ext
  · funext i
    change (0:ZMod 2) = (Pi.single a.val 1 : OriginalWittQuotient.Bits (Fin n) κ) (Sum.inl i.val)
    have h := a.property i.val i.property
    simp [Pi.single_apply,Ne.symm h]
  · funext j
    have he : (originals κ n I).symm (Sum.inr j) = a.val ↔
        j = GlobalSelectedColumns.rowEquiv κ n I a := by
      constructor
      · intro h
        have hh := congrArg (originals κ n I) h
        rw [Equiv.apply_symm_apply,ExplicitStratumCoordinates.row_originals] at hh
        exact Sum.inr.inj hh
      · intro h
        subst j
        exact (Equiv.eq_symm_apply _).mp
          (ExplicitStratumCoordinates.row_originals κ n I a).symm
    change ((Finsupp.single (GlobalSelectedColumns.rowEquiv κ n I a) (1:ℤ)) j : ZMod 2) =
      (Pi.single a.val 1 : OriginalWittQuotient.Bits (Fin n) κ) ((originals κ n I).symm (Sum.inr j))
    simp [Finsupp.single_apply,Pi.single_apply,apply_ite,he,eq_comm]

#print axioms single
end Verification.OriginalWittOriginalExponent
