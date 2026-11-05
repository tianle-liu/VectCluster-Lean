/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenDifferential
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Powerset

/-!
# Graph Cover

Concrete combinatorics behind manuscript Lemma graph-cover: exact fibers over
cover subsets, the surviving dominating subsets, and an explicit contraction
of every nonempty augmented simplex fiber. No acyclic matching assumption is used.
-/

namespace Verification.GraphCover

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (C T : Finset V)

/-- Every edge has an endpoint in the chosen cover. -/
def Covers : Prop := ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C

noncomputable def remaining (I : Finset V) : Finset V := by
  classical
  exact (T \ C).filter (fun v => ∀ i ∈ I, ¬ G.Adj i v)

/-- Independent simplices of the induced graph on T, including the empty simplex. -/
abbrev Simplex := {J : Finset V // J ⊆ T ∧ G.IsIndepSet (J : Set V)}

abbrev CoverSimplex := {I : Finset V // I ⊆ T ∩ C ∧ G.IsIndepSet (I : Set V)}

abbrev Fiber (I : CoverSimplex G C T) := {K : Finset V // K ⊆ remaining G C T I.val}

omit [DecidableEq V] in
theorem independent_not_adj {I : Finset V} (hI : G.IsIndepSet (I : Set V))
    {i j : V} (hi : i ∈ I) (hj : j ∈ I) : ¬ G.Adj i j := by
  by_cases h : i = j
  · subst j; exact G.irrefl
  · exact hI hi hj h

theorem mem_remaining (I : Finset V) (v : V) :
    v ∈ remaining G C T I ↔ v ∈ T ∧ v ∉ C ∧ ∀ i ∈ I, ¬ G.Adj i v := by
  classical
  simp only [remaining, Finset.mem_filter, Finset.mem_sdiff]
  tauto

theorem outside_independent (hC : Covers G C) : G.IsIndepSet ((T \ C : Finset V) : Set V) := by
  intro i hi j hj _ hadj
  rcases hC i j hadj with hc | hc
  · exact (Finset.mem_sdiff.mp hi).2 hc
  · exact (Finset.mem_sdiff.mp hj).2 hc

theorem remaining_antitone {I J : Finset V} (h : I ⊆ J) :
    remaining G C T J ⊆ remaining G C T I := by
  intro v hv
  obtain ⟨hT,hC,hn⟩ := (mem_remaining G C T J v).mp hv
  exact (mem_remaining G C T I v).mpr ⟨hT,hC,fun i hi => hn i (h hi)⟩

theorem fiber_union_independent (hC : Covers G C) (I : CoverSimplex G C T)
    (K : Fiber G C T I) : G.IsIndepSet ((I.val ∪ K.val : Finset V) : Set V) := by
  intro i hi j hj hij hadj
  rcases Finset.mem_union.mp hi with hi | hi
  · rcases Finset.mem_union.mp hj with hj | hj
    · exact I.property.2 hi hj hij hadj
    · exact ((mem_remaining G C T I.val j).mp (K.property hj)).2.2 i hi hadj
  · rcases Finset.mem_union.mp hj with hj | hj
    · exact ((mem_remaining G C T I.val i).mp (K.property hi)).2.2 j hj hadj.symm
    · have hiC := ((mem_remaining G C T I.val i).mp (K.property hi)).2.1
      have hjC := ((mem_remaining G C T I.val j).mp (K.property hj)).2.1
      exact (hC i j hadj).elim hiC hjC

def fiberUnion (hC : Covers G C) (x : Σ I : CoverSimplex G C T, Fiber G C T I) :
    Simplex G T :=
  ⟨x.1.val ∪ x.2.val, by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_inter.mp (x.1.property.1 hv)).1
    · exact ((mem_remaining G C T x.1.val v).mp (x.2.property hv)).1,
    fiber_union_independent G C T hC x.1 x.2⟩

def splitSimplex (J : Simplex G T) : Σ I : CoverSimplex G C T, Fiber G C T I := by
  refine ⟨⟨J.val ∩ C, ?_, ?_⟩, ⟨J.val \ C, ?_⟩⟩
  · intro v hv
    exact Finset.mem_inter.mpr
      ⟨J.property.1 (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
  · exact J.property.2.mono (by intro v hv; exact (Finset.mem_inter.mp hv).1)
  · intro v hv
    obtain ⟨hvJ,hvC⟩ := Finset.mem_sdiff.mp hv
    apply (mem_remaining G C T (J.val ∩ C) v).mpr
    exact ⟨J.property.1 hvJ, hvC, fun i hi =>
      independent_not_adj G J.property.2 (Finset.mem_inter.mp hi).1 hvJ⟩

theorem fiber_cover_part (I : CoverSimplex G C T) (K : Fiber G C T I) :
    (I.val ∪ K.val) ∩ C = I.val := by
  ext v
  constructor
  · intro hv
    obtain ⟨hU,hC⟩ := Finset.mem_inter.mp hv
    rcases Finset.mem_union.mp hU with hi | hk
    · exact hi
    · exact False.elim (((mem_remaining G C T I.val v).mp (K.property hk)).2.1 hC)
  · intro hv
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hv,
      (Finset.mem_inter.mp (I.property.1 hv)).2⟩

theorem fiber_outside_part (I : CoverSimplex G C T) (K : Fiber G C T I) :
    (I.val ∪ K.val) \ C = K.val := by
  ext v
  constructor
  · intro hv
    obtain ⟨hU,hC⟩ := Finset.mem_sdiff.mp hv
    rcases Finset.mem_union.mp hU with hi | hk
    · exact False.elim (hC (Finset.mem_inter.mp (I.property.1 hi)).2)
    · exact hk
  · intro hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hv,
      ((mem_remaining G C T I.val v).mp (K.property hv)).2.1⟩

/-- Exact decomposition of actual graph simplices into the cover part and a full simplex fiber. -/
def simplexFiberEquiv (hC : Covers G C) :
    Simplex G T ≃ Σ I : CoverSimplex G C T, Fiber G C T I where
  toFun := splitSimplex G C T
  invFun := fiberUnion G C T hC
  left_inv J := by
    apply Subtype.ext
    change J.val ∩ C ∪ J.val \ C = J.val
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  right_inv x := by
    apply Sigma.ext (Subtype.ext (fiber_cover_part G C T x.1 x.2))
    apply (Subtype.heq_iff_coe_eq (by
      intro K
      change K ⊆ remaining G C T ((x.1.val ∪ x.2.val) ∩ C) ↔ _
      rw [fiber_cover_part G C T x.1 x.2])).mpr
    exact fiber_outside_part G C T x.1 x.2

/-- Domination is exactly the empty-fiber condition. -/
def Dominates (I : Finset V) : Prop := ∀ v ∈ T \ C, ∃ i ∈ I, G.Adj i v

theorem remaining_empty_iff (I : Finset V) :
    remaining G C T I = ∅ ↔ Dominates G C T I := by
  classical
  rw [Finset.eq_empty_iff_forall_not_mem]
  constructor
  · intro h v hv
    by_contra hn
    apply h v
    simp only [remaining, Finset.mem_filter]
    exact ⟨hv, by simpa only [not_exists, not_and] using hn⟩
  · intro h v hv
    obtain ⟨hvT,hvC,hn⟩ := (mem_remaining G C T I v).mp hv
    obtain ⟨i,hi,hadj⟩ := h v (Finset.mem_sdiff.mpr ⟨hvT,hvC⟩)
    exact hn i hi hadj

theorem dominates_mono {I J : Finset V} (h : I ⊆ J) (hI : Dominates G C T I) :
    Dominates G C T J := by
  intro v hv
  obtain ⟨i,hi,hadj⟩ := hI v hv
  exact ⟨i,h hi,hadj⟩

/-- Exactly the basis labels retained by the manuscript's chain quotient. -/
def Survives (J : Simplex G T) : Prop := J.val ⊆ C ∧ Dominates G C T J.val

theorem survives_iff_empty_remaining (J : Simplex G T) :
    Survives G C T J ↔ remaining G C T (J.val ∩ C) = ∅ := by
  constructor
  · intro h
    rw [Finset.inter_eq_left.mpr h.1]
    exact (remaining_empty_iff G C T J.val).mpr h.2
  · intro h
    have hK : J.val \ C = ∅ := Finset.eq_empty_iff_forall_not_mem.mpr (by
      intro v hv
      have hm := (splitSimplex G C T J).2.property hv
      change v ∈ remaining G C T (J.val ∩ C) at hm
      rw [h] at hm
      exact Finset.not_mem_empty v hm)
    have hJC : J.val ⊆ C := Finset.sdiff_eq_empty_iff_subset.mp hK
    exact ⟨hJC, by
      apply (remaining_empty_iff G C T J.val).mp
      simpa only [Finset.inter_eq_left.mpr hJC] using h⟩

/-- Surviving simplices are closed under independent cofaces. Dually the killed
simplices form the chain subcomplex stated in the paper. -/
theorem survives_upward (J K : Simplex G T) (hJK : J.val ⊆ K.val)
    (hJ : Survives G C T J) : Survives G C T K := by
  refine ⟨?_, dominates_mono G C T hJK hJ.2⟩
  intro v hv
  by_contra hvC
  obtain ⟨i,hi,hadj⟩ := hJ.2 v (Finset.mem_sdiff.mpr ⟨K.property.1 hv,hvC⟩)
  exact independent_not_adj G K.property.2 (hJK hi) hv hadj

theorem killed_downward (J K : Simplex G T) (hJK : J.val ⊆ K.val)
    (hK : ¬ Survives G C T K) : ¬ Survives G C T J :=
  fun hJ => hK (survives_upward G C T J K hJK hJ)

/-- The maximum independent cardinality inside the cover, computed as a finite maximum. -/
noncomputable def coverRank : ℕ := by
  classical
  exact (C.powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V))).sup Finset.card

theorem independent_card_le_coverRank (I : Finset V) (hIC : I ⊆ C)
    (hI : G.IsIndepSet (I : Set V)) : I.card ≤ coverRank G C := by
  classical
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hIC,hI⟩)

theorem survivor_degree_bound (J : Simplex G T) (hJ : Survives G C T J) :
    J.val.card ≤ coverRank G C :=
  independent_card_le_coverRank G C J.val hJ.1 J.property.2

#print axioms Covers
#print axioms remaining
#print axioms independent_not_adj
#print axioms mem_remaining
#print axioms outside_independent
#print axioms remaining_antitone
#print axioms fiber_union_independent
#print axioms fiberUnion
#print axioms splitSimplex
#print axioms fiber_cover_part
#print axioms fiber_outside_part
#print axioms simplexFiberEquiv
#print axioms Dominates
#print axioms remaining_empty_iff
#print axioms dominates_mono
#print axioms Survives
#print axioms survives_iff_empty_remaining
#print axioms survives_upward
#print axioms killed_downward
#print axioms coverRank
#print axioms independent_card_le_coverRank
#print axioms survivor_degree_bound

end Verification.GraphCover

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.GraphCover.CoverSimplex
#print axioms Verification.GraphCover.Fiber
#print axioms Verification.GraphCover.Simplex
