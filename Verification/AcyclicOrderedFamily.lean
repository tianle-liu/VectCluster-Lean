/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AcyclicMatrixOrder
import Verification.RealAcyclicFiltration
import Verification.FrozenAcyclicCover

/-!
# Acyclic Ordered Family

The actual anticlique family agrees with the family used by the
ordered acyclic chart construction, after topological numbering.
-/
noncomputable section
namespace Verification.AcyclicOrderedFamily
open AcyclicMatrixOrder
variable {V C : Type} [Fintype V]
variable (B : (V ⊕ C) → V → ℤ)
variable (h : ∀ v,¬ Relation.TransGen (fun a i => 0<B (Sum.inl a) i) v v)

def fullMatrix (a : Fin (Fintype.card V) ⊕ C) : (Fin (Fintype.card V) ⊕ Empty) → ℤ :=
  Sum.elim (matrix B h a) Empty.elim

def family (I : Finset (Fin (Fintype.card V))) : Prop :=
  ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights C (Fintype.card V) (fullMatrix B h)) I

variable (w : V → ℤ) (hw : ∀ i,0<w i)
variable (hB : ∀ a i,w a*B (Sum.inl a) i=-(w i*B (Sum.inl i) a))

include hw hB in
theorem ordered_iff (I : Finset (Fin (Fintype.card V))) :
    family B h I ↔ ExchangeReindex.PrincipalIndependent (matrix B h) I := by
  constructor
  · intro hi a ha i hi' _
    exact RealAcyclicFiltration.independent_zero_block (matrix B h)
      (positive_support B h) (negative_support B h w hw hB)
      (paired_support B h w hw hB) I hi ⟨a,ha⟩ ⟨i,hi'⟩
  · intro hi a ha i hi' hadj
    rcases hadj with ⟨hai,hv⟩ | ⟨hia,hv⟩
    · have hz := hi i hi' a ha (ne_of_gt hai)
      apply hv
      change (-matrix B h (Sum.inl i) a).toNat=0
      rw [hz]
      rfl
    · have hz := hi a ha i hi' (ne_of_gt hia)
      apply hv
      change (-matrix B h (Sum.inl a) i).toNat=0
      rw [hz]
      rfl

include hw hB in
theorem source_iff (I : Finset (Fin (Fintype.card V))) :
    ExchangeReindex.PrincipalIndependent B (I.map (enumeration B h).toEmbedding) ↔ family B h I :=
  (ExchangeReindex.independent_iff (enumeration B h) B I).trans (ordered_iff B h w hw hB I).symm

omit [Fintype V] in
theorem down (I J : Finset V) (hJI : J⊆I)
    (hI : ExchangeReindex.PrincipalIndependent B I) : ExchangeReindex.PrincipalIndependent B J :=
  fun a ha i hi => hI a (hJI ha) i (hJI hi)

omit [Fintype V] in
include hw hB in
theorem zeroBlock (I : Finset V) (hI : ExchangeReindex.PrincipalIndependent B I)
    (a i : I) : B (Sum.inl a.val) i.val=0 := by
  by_cases he : a.val=i.val
  · rw [he]
    exact SkewSymmetrizableSigns.diagonal (fun a i => B (Sum.inl a) i) w hw hB i.val
  · exact hI a.val a.property i.val i.property he

#print axioms fullMatrix
#print axioms family
#print axioms ordered_iff
#print axioms source_iff
#print axioms down
#print axioms zeroBlock
end Verification.AcyclicOrderedFamily
