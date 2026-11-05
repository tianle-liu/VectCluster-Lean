/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphCoverMatrices
import Verification.GraphBlockComplex

/-!
# Graph Chain Cochain

Literal transposition of the augmented signed graph boundary and the
independence coboundary, with an explicit finite-simplex index bijection.
-/

namespace Verification.GraphChainCochain

open Classical
open Verification.GraphCover Verification.GraphSimplexChains
  Verification.GraphBlocks Verification.GraphBlockComplex Verification.EvenDifferential

variable {R : Type} [CommRing R] {V C : Type}
  [Fintype V] [LinearOrder V] [DecidableEq C]
  (G : SimpleGraph V) (c : V → C) (T : Finset V)

/-- Both original models use the same independent subset, with the two predicates reordered. -/
def chainCochainIndex : Simplex G T ≃ SimplexIndex G c (T,∅) where
  toFun J := ⟨J.val,J.property.2,by simpa [available] using J.property.1⟩
  invFun J := ⟨J.val,by simpa [available] using J.property.2,J.property.1⟩
  left_inv J := by apply Subtype.ext; rfl
  right_inv J := by apply Subtype.ext; rfl

omit [Fintype V] in
theorem rankBelow_erase_self (J : Finset V) (i : V) : rankBelow (J.erase i) i=rankBelow J i := by
  simp [rankBelow,Finset.filter_erase]

omit [Fintype V] in
/-- Every deletion face is exactly the reverse of an allowed coface, including endpoints. -/
theorem face_iff_coface (J K : Simplex G T) (i : V) :
    (i ∈ J.val ∧ eraseSimplex G T J i=K) ↔
      ∃ hi : simplexCanAdd G c (T,∅) (chainCochainIndex G c T K) i,
        addSimplex G c (T,∅) (chainCochainIndex G c T K) i hi=chainCochainIndex G c T J := by
  constructor
  · rintro ⟨hi,rfl⟩
    have ha : simplexCanAdd G c (T,∅) (chainCochainIndex G c T (eraseSimplex G T J i)) i := by
      refine ⟨?_,?_,?_⟩
      · simpa [available] using J.property.1 hi
      · exact Finset.not_mem_erase _ _
      · change G.IsIndepSet ((insert i (J.val.erase i) : Finset V) : Set V)
        rw [Finset.insert_erase hi]
        exact J.property.2
    refine ⟨ha,?_⟩
    apply Subtype.ext
    exact Finset.insert_erase hi
  · rintro ⟨hi,he⟩
    have hv : insert i K.val=J.val := congrArg Subtype.val he
    refine ⟨hv ▸ Finset.mem_insert_self _ _,?_⟩
    apply Subtype.ext
    change J.val.erase i=K.val
    have hki : i ∉ K.val := hi.2.1
    rw [←hv,Finset.erase_insert hki]

/-- Exact coefficient identity: the two independently defined differentials are transposes. -/
theorem incidence_transpose (J K : Simplex G T) :
    simplexBasisDifferential R G c (T,∅) (chainCochainIndex G c T K)
      (chainCochainIndex G c T J)=basisBoundary (R := R) G T J K := by
  have hb : basisBoundary (R := R) G T J K = ∑ i : V,
      if i ∈ J.val then
        (Finsupp.single (eraseSimplex G T J i) ((-1 : R)^rankBelow J.val i)) K else 0 := by
    simp [basisBoundary,Finsupp.finset_sum_apply]
  rw [hb]
  simp only [simplexBasisDifferential,Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hj : i ∈ J.val
  · rw [if_pos hj]
    by_cases he : eraseSimplex G T J i=K
    · obtain ⟨hi,ha⟩ := (face_iff_coface G c T J K i).mp ⟨hj,he⟩
      rw [dif_pos hi,ha,he,Finsupp.single_eq_same,Finsupp.single_eq_same]
      rw [←he]
      change (-1 : R)^rankBelow (J.val.erase i) i=(-1)^rankBelow J.val i
      rw [rankBelow_erase_self]
    · rw [Finsupp.single_eq_of_ne he]
      by_cases hi : simplexCanAdd G c (T,∅) (chainCochainIndex G c T K) i
      · rw [dif_pos hi]
        apply Finsupp.single_eq_of_ne
        intro ha
        exact he ((face_iff_coface G c T J K i).mpr ⟨hi,ha⟩).2
      · rw [dif_neg hi,Finsupp.zero_apply]
  · rw [if_neg hj]
    by_cases hi : simplexCanAdd G c (T,∅) (chainCochainIndex G c T K) i
    · rw [dif_pos hi]
      apply Finsupp.single_eq_of_ne
      intro ha
      exact hj ((face_iff_coface G c T J K i).mpr ⟨hi,ha⟩).1
    · rw [dif_neg hi,Finsupp.zero_apply]

#print axioms chainCochainIndex
#print axioms rankBelow_erase_self
#print axioms face_iff_coface
#print axioms incidence_transpose

end Verification.GraphChainCochain
