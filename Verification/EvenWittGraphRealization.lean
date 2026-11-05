/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenWittColorVanishing
import Verification.GraphBlocks
import Verification.OriginalWittIntegerComplex

/-!
# Even Witt Graph Realization

The proved literal Pfister residue assembles to the actual graph
monomial differential on all strata, preserving its incidence signs.
-/
noncomputable section
open scoped Classical BigOperators
namespace Verification.EvenWittGraphRealization
open Verification.OriginalWittIntegerDifferential Verification.OriginalWittQuotient
open Verification.GraphBlocks Verification.EvenWittPfisterResidue
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder V]
variable (G : SimpleGraph V) (c : V → C)

abbrev Allowed := fun I : Finset V => G.IsIndepSet (I : Set V)
abbrev Coefficients := Cochains (EvenWittColumns.frozenMatrix c) (Allowed G)

def hereditary : ∀ I J, J ⊆ I → Allowed G I → Allowed G J := by
  intro I J h hI
  exact hI.mono (by intro j hj; exact h hj)

def independentEntries : ∀ I, Allowed G I → ∀ i∈I, ∀ j∈I, i≠j →
    EvenWittColumns.frozenMatrix c (Sum.inl j) i = 0 := by
  intros
  rfl

def word (x : MonomialIndex G c) : Coefficients G c :=
  fun J => if J.val = x.I then quotientWord c J.val x.A x.F else 0

def realization : (MonomialIndex G c →₀ ℤ) →ₗ[ℤ] Coefficients G c :=
  Finsupp.linearCombination ℤ (word G c)

omit [Fintype V] [Fintype C] in
theorem single (x : MonomialIndex G c) (r : ℤ) :
    realization G c (Finsupp.single x r) = r • word G c x :=
  Finsupp.linearCombination_single ℤ r x

omit [Fintype V] [Fintype C] in
theorem face_word (x : MonomialIndex G c) (J : Index (Allowed G)) (i : J.val) :
    SubsetProjectionComplex.sign J.val i.val •
      residue (EvenWittColumns.frozenMatrix c) (J.val.erase i.val) J.val i.val (Finset.erase_subset _ _)
        (Finset.not_mem_erase _ _) (fun _ => rfl)
        (word G c x (predecessor (Allowed G) (hereditary G) J i)) =
    if h : CanAdd x i.val then incidence ℤ x.I i.val • word G c (addMonomial x i.val h) J else 0 := by
  simp only [word,predecessor]
  by_cases hI : J.val.erase i.val = x.I
  · have hJ : J.val = insert i.val x.I := by rw [← hI,Finset.insert_erase i.property]
    have hind : G.IsIndepSet ((insert i.val x.I : Finset V) : Set V) := hJ ▸ J.property
    rw [if_pos hI,EvenWittColorVanishing.residue c _ _ _ _ _ i.property]
    have hs : SubsetProjectionComplex.sign J.val i.val = incidence ℤ x.I i.val := by
      unfold SubsetProjectionComplex.sign incidence
      congr 1
      apply congrArg Finset.card
      ext j
      by_cases hj : j = i.val <;> simp [hJ,hj]
    rw [hs]
    by_cases h : CanAdd x i.val
    · have hh : i.val ∈ x.A ∧ c i.val ∉ x.F := ⟨h.1,h.2.1⟩
      simp only [dif_pos h,if_pos hh,addMonomial,if_pos hJ]
      congr 2
      ext a
      simp
    · have hn : ¬ (i.val ∈ x.A ∧ c i.val ∉ x.F) := fun ha => h ⟨ha.1,ha.2,hind⟩
      simp only [dif_neg h,if_neg hn,smul_zero]
  · rw [if_neg hI,map_zero,smul_zero]
    by_cases h : CanAdd x i.val
    · have hiI : i.val ∉ x.I := fun hi => Finset.disjoint_left.mp x.disjoint hi h.1
      have hn : J.val ≠ insert i.val x.I := by
        intro he
        apply hI
        exact (congrArg (fun S : Finset V => S.erase i.val) he).trans (Finset.erase_insert hiI)
      simp only [dif_pos h,addMonomial,if_neg hn,smul_zero]
    · rw [dif_neg h]

omit [Fintype V] [Fintype C] in
theorem outside (x : MonomialIndex G c) (J : Index (Allowed G)) (i : V) (hi : i ∉ J.val) :
    (if h : CanAdd x i then incidence ℤ x.I i • word G c (addMonomial x i h) J else 0) = 0 := by
  by_cases h : CanAdd x i
  · have hn : J.val ≠ insert i x.I := fun he => hi (he ▸ Finset.mem_insert_self i x.I)
    simp [h,word,addMonomial,hn]
  · simp [h]

omit [Fintype C] in
theorem differential_word (x : MonomialIndex G c) :
    OriginalWittIntegerDifferential.differential (EvenWittColumns.frozenMatrix c) (Allowed G)
      (hereditary G) (independentEntries G c) (word G c x) =
      realization G c (monomialBasisDifferential ℤ x) := by
  funext J
  change (∑ i : J.val, _) = _
  trans ∑ i : J.val, (if h : CanAdd x i.val then
    incidence ℤ x.I i.val • word G c (addMonomial x i.val h) J else 0)
  · apply Finset.sum_congr rfl
    intro i _
    exact face_word G c x J i
  · trans ∑ i ∈ J.val, (if h : CanAdd x i then incidence ℤ x.I i • word G c (addMonomial x i h) J else 0)
    · exact Finset.sum_coe_sort J.val (fun i : V => if h : CanAdd x i then
        incidence ℤ x.I i • word G c (addMonomial x i h) J else 0)
    trans ∑ i : V, (if h : CanAdd x i then incidence ℤ x.I i • word G c (addMonomial x i h) J else 0)
    · apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      exact outside G c x J i hi
    · simp only [monomialBasisDifferential,map_sum,Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : CanAdd x i
      · simp only [dif_pos h,single,Pi.smul_apply]
      · simp only [dif_neg h,map_zero,Pi.zero_apply]

#print axioms Allowed
#print axioms Coefficients
#print axioms hereditary
#print axioms independentEntries
#print axioms word
#print axioms realization
#print axioms single
#print axioms face_word
#print axioms outside
#print axioms differential_word
end Verification.EvenWittGraphRealization
