/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AcyclicEnumeration
import Verification.ExchangeReindex
import Verification.SkewSymmetrizableSigns

/-!
# Acyclic Matrix Order

The triangular sign support used in the geometric constructions follows
from the manuscript's actual directed acyclicity and positive symmetrizer.
-/
noncomputable section
namespace Verification.AcyclicMatrixOrder
variable {V C : Type} [Fintype V]
variable (B : (V ⊕ C) → V → ℤ)
variable (h : ∀ v,¬ Relation.TransGen (fun a i => 0<B (Sum.inl a) i) v v)

def enumeration : Fin (Fintype.card V) ≃ V :=
  AcyclicEnumeration.enumeration (fun a i => 0<B (Sum.inl a) i) h

def matrix : (Fin (Fintype.card V) ⊕ C) → Fin (Fintype.card V) → ℤ :=
  ExchangeReindex.matrix (enumeration B h) B

theorem positive_lt (a i : Fin (Fintype.card V)) (hp : 0<matrix B h (Sum.inl a) i) : a<i := by
  have hi := AcyclicEnumeration.index_lt (fun a i => 0<B (Sum.inl a) i) h
    (enumeration B h a) (enumeration B h i) hp
  change (enumeration B h).symm ((enumeration B h) a)<
    (enumeration B h).symm ((enumeration B h) i) at hi
  simpa only [Equiv.symm_apply_apply] using hi

theorem positive_support (a i : Fin (Fintype.card V)) (hn : ¬a<i) :
    (matrix B h (Sum.inl a) i).toNat=0 := by
  apply Int.toNat_eq_zero.mpr
  exact le_of_not_gt (fun hp => hn (positive_lt B h a i hp))

variable (w : V → ℤ) (hw : ∀ i,0<w i)
variable (hB : ∀ a i,w a*B (Sum.inl a) i=-(w i*B (Sum.inl i) a))

include hw hB in
theorem negative_support (a i : Fin (Fintype.card V)) (hn : ¬i<a) :
    (-matrix B h (Sum.inl a) i).toNat=0 := by
  apply Int.toNat_eq_zero.mpr
  have hz : 0≤matrix B h (Sum.inl a) i := by
    apply le_of_not_gt
    intro hp
    have he := (SkewSymmetrizableSigns.sign_iff (fun a i => B (Sum.inl a) i)
      w hw hB (enumeration B h i) (enumeration B h a)).mpr hp
    exact hn (positive_lt B h i a he)
  omega

include hw hB in
theorem paired_support (a i : Fin (Fintype.card V)) :
    (matrix B h (Sum.inl a) i).toNat=0 ↔ (-matrix B h (Sum.inl i) a).toNat=0 := by
  rw [Int.toNat_eq_zero,Int.toNat_eq_zero]
  have he := SkewSymmetrizableSigns.sign_iff (fun a i => B (Sum.inl a) i)
    w hw hB (enumeration B h a) (enumeration B h i)
  change 0<B (Sum.inl (enumeration B h a)) (enumeration B h i) ↔
    B (Sum.inl (enumeration B h i)) (enumeration B h a)<0 at he
  change B (Sum.inl (enumeration B h a)) (enumeration B h i)≤0 ↔
    -B (Sum.inl (enumeration B h i)) (enumeration B h a)≤0
  omega

#print axioms enumeration
#print axioms matrix
#print axioms positive_lt
#print axioms positive_support
#print axioms negative_support
#print axioms paired_support
end Verification.AcyclicMatrixOrder
