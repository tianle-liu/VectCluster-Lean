/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphBlocks
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Graph Block Square

Square-zero of the independently defined induced-simplex incidence differential.
The proof pairs the two orders of adjoining distinct vertices.
-/

namespace Verification.GraphBlockSquare

open Verification.GraphBlocks

variable {V C : Type*} [DecidableEq V] [DecidableEq C]
  {G : SimpleGraph V} {c : V → C}

theorem canAddBlock_reverse (b : BlockIndex G c) (i : V) (hi : CanAddBlock b i)
    (j : V) (hj : CanAddBlock (addBlock b i hi) j) :
    ∃ hj' : CanAddBlock b j, CanAddBlock (addBlock b j hj') i := by
  have hji : j ≠ i := by
    intro h
    exact hj.2.1 (by simp [addBlock, h])
  have hjI : j ∉ b.I := by
    intro h
    exact hj.2.1 (Finset.mem_insert_of_mem h)
  have hindj : G.IsIndepSet ((insert j b.I : Finset V) : Set V) := by
    apply hj.2.2.mono
    intro v hv
    exact Finset.mem_insert.mpr ((Finset.mem_insert.mp hv).imp_right Finset.mem_insert_of_mem)
  let hj' : CanAddBlock b j := ⟨hj.1, hjI, hindj⟩
  refine ⟨hj', hi.1, ?_, ?_⟩
  · simp [addBlock, Ne.symm hji, hi.2.1]
  · simpa only [addBlock, Finset.insert_comm] using hj.2.2

theorem addBlock_comm (b : BlockIndex G c) (i j : V)
    (hi : CanAddBlock b i) (hj : CanAddBlock (addBlock b i hi) j)
    (hj' : CanAddBlock b j) (hi' : CanAddBlock (addBlock b j hj') i) :
    addBlock (addBlock b i hi) j hj = addBlock (addBlock b j hj') i hi' := by
  apply BlockIndex.ext <;> simp [addBlock, Finset.insert_comm]

variable (R : Type*) [CommRing R] [LinearOrder V]

theorem incidence_insert (I : Finset V) (i j : V) (hj : j ∉ I) :
    incidence R (insert j I) i = if j < i then -incidence R I i else incidence R I i := by
  classical
  by_cases hji : j < i
  · have hnot : j ∉ I.filter (· < i) := by simp [hj]
    simp [incidence, Finset.filter_insert, hji, Finset.card_insert_of_not_mem hnot, pow_succ]
  · simp [incidence, Finset.filter_insert, hji]

theorem incidence_products_opposite (I : Finset V) (i j : V)
    (hi : i ∉ I) (hj : j ∉ I) (hij : i ≠ j) :
    incidence R I i * incidence R (insert i I) j =
      -(incidence R I j * incidence R (insert j I) i) := by
  rw [incidence_insert R I j i hi, incidence_insert R I i j hj]
  rcases lt_or_gt_of_ne hij with h | h
  · simp [h, not_lt_of_ge h.le, mul_comm]
  · simp [h, not_lt_of_ge h.le, mul_comm]

noncomputable def twoStep (b : BlockIndex G c) (i j : V) : BlockIndex G c →₀ R := by
  classical
  exact if hi : CanAddBlock b i then
    if hj : CanAddBlock (addBlock b i hi) j then
      Finsupp.single (addBlock (addBlock b i hi) j hj)
        (incidence R b.I i * incidence R (insert i b.I) j)
    else 0
  else 0

theorem twoStep_success_opposite (b : BlockIndex G c) (i j : V)
    (hi : CanAddBlock b i) (hj : CanAddBlock (addBlock b i hi) j) :
    twoStep R b i j = -twoStep R b j i := by
  classical
  obtain ⟨hj', hi'⟩ := canAddBlock_reverse b i hi j hj
  have hij : i ≠ j := by
    intro h
    exact hj.2.1 (by simp [addBlock, h])
  simp only [twoStep, dif_pos hi, dif_pos hj, dif_pos hj', dif_pos hi']
  rw [addBlock_comm b i j hi hj hj' hi', incidence_products_opposite R b.I i j hi.2.1 hj'.2.1 hij,
    Finsupp.single_neg]

theorem twoStep_opposite (b : BlockIndex G c) (i j : V) :
    twoStep R b i j = -twoStep R b j i := by
  classical
  by_cases hi : CanAddBlock b i
  · by_cases hj : CanAddBlock (addBlock b i hi) j
    · exact twoStep_success_opposite R b i j hi hj
    · have hno : ∀ hj' : CanAddBlock b j, ¬CanAddBlock (addBlock b j hj') i := by
        intro hj' hi'
        obtain ⟨_, hj''⟩ := canAddBlock_reverse b j hj' i hi'
        exact hj hj''
      simp only [twoStep, dif_pos hi, dif_neg hj]
      split <;> simp_all
  · have hno : ∀ hj' : CanAddBlock b j, ¬CanAddBlock (addBlock b j hj') i := by
      intro hj' hi'
      obtain ⟨hi'', _⟩ := canAddBlock_reverse b j hj' i hi'
      exact hi hi''
    simp only [twoStep, dif_neg hi]
    split <;> simp_all

theorem twoStep_same (b : BlockIndex G c) (i : V) : twoStep R b i i = 0 := by
  classical
  unfold twoStep
  split
  · rename_i hi
    have hn : ¬CanAddBlock (addBlock b i hi) i := by
      intro h
      exact h.2.1 (by simp [addBlock])
    simp [hn]
  · rfl

variable [Fintype V]

theorem blockBasisDifferential_squared (b : BlockIndex G c) :
    blockDifferential R (blockBasisDifferential R b) = 0 := by
  classical
  have hexpand : blockDifferential R (blockBasisDifferential R b) =
      ∑ i : V, ∑ j : V, twoStep R b i j := by
    unfold blockBasisDifferential
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : CanAddBlock b i
    · simp only [dif_pos hi, blockDifferential, Finsupp.linearCombination_single]
      unfold blockBasisDifferential
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : CanAddBlock (addBlock b i hi) j
      · simp [twoStep, hi, hj, Finsupp.smul_single, addBlock]
      · simp [twoStep, hi, hj]
    · simp [hi, twoStep, map_zero]
  rw [hexpand, ← Finset.sum_product']
  apply Finset.sum_involution (fun p _ => (p.2, p.1))
  · intro p _
    exact eq_neg_iff_add_eq_zero.mp (twoStep_opposite R b p.1 p.2)
  · intro p _ hn he
    have h : p.1 = p.2 := congrArg Prod.snd he
    exact hn (by simpa [h] using twoStep_same R b p.2)
  · intro p _
    simp
  · intro p _
    cases p
    rfl

theorem blockDifferential_squared :
    (blockDifferential (G := G) (c := c) R).comp (blockDifferential R) = 0 := by
  apply Finsupp.lhom_ext
  intro b r
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, blockDifferential,
    Finsupp.linearCombination_single, map_smul]
  change r • blockDifferential R (blockBasisDifferential R b) = 0
  rw [blockBasisDifferential_squared, smul_zero]

#print axioms canAddBlock_reverse
#print axioms addBlock_comm
#print axioms incidence_insert
#print axioms incidence_products_opposite
#print axioms twoStep
#print axioms twoStep_success_opposite
#print axioms twoStep_opposite
#print axioms twoStep_same
#print axioms blockBasisDifferential_squared
#print axioms blockDifferential_squared

end Verification.GraphBlockSquare
