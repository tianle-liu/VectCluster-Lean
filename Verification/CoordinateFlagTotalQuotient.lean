/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateFlag
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coordinate Flag Total Quotient

Successive old-coordinate and last-coordinate quotients are the
literal full coordinate quotient, retaining every original element.
-/
noncomputable section
namespace Verification.CoordinateFlagTotalQuotient
open Verification.CoordinateFlag
variable (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] (x : ι → A) (v : ι)

def lastIdeal : Ideal A := Ideal.span {x v}

theorem old_sup_last : oldIdeal A ι x v ⊔ lastIdeal A ι x v = ConormalFrame.ideal x := by
  classical
  apply le_antisymm
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Ideal.subset_span (Set.mem_range_self i.val)
    · apply Ideal.span_le.mpr
      rintro a ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      exact Ideal.subset_span (Set.mem_range_self v)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases hi : i = v
    · subst i
      exact (show lastIdeal A ι x v ≤ oldIdeal A ι x v ⊔ lastIdeal A ι x v from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton _))
    · exact (show oldIdeal A ι x v ≤ oldIdeal A ι x v ⊔ lastIdeal A ι x v from le_sup_left)
        (Ideal.subset_span ⟨⟨i,hi⟩,rfl⟩)

theorem map_last : (lastIdeal A ι x v).map (Ideal.Quotient.mkₐ R (oldIdeal A ι x v)) =
    finalIdeal A ι x v := by
  rw [lastIdeal,Ideal.map_span,Set.image_singleton]
  rfl

def equiv : ClosedAll A ι x v ≃ₐ[R] A ⧸ ConormalFrame.ideal x :=
  (Ideal.quotientEquivAlgOfEq R (map_last R A ι x v).symm).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ R (oldIdeal A ι x v) (lastIdeal A ι x v)).trans
      (Ideal.quotientEquivAlgOfEq R (old_sup_last A ι x v)))

theorem equiv_mk (a : A) : equiv R A ι x v
    (Ideal.Quotient.mk (finalIdeal A ι x v) (Ideal.Quotient.mk (oldIdeal A ι x v) a)) =
      Ideal.Quotient.mk (ConormalFrame.ideal x) a := by
  dsimp only [equiv,AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  change Ideal.quotientEquivAlgOfEq R _
    (DoubleQuot.quotQuotEquivQuotSup (oldIdeal A ι x v) (lastIdeal A ι x v)
      (DoubleQuot.quotQuotMk (oldIdeal A ι x v) (lastIdeal A ι x v) a)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk,Ideal.quotientEquivAlgOfEq_mk]

#print axioms lastIdeal
#print axioms old_sup_last
#print axioms map_last
#print axioms equiv
#print axioms equiv_mk
end Verification.CoordinateFlagTotalQuotient
