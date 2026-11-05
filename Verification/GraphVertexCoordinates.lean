/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphChainMatrix
import Verification.IncidenceSaturation

/-!
# Graph Vertex Coordinates

Literal degree-zero (one-vertex) chain coordinates and the signed edge
boundaries needed for the integral low-dimensional freeness argument.
-/

namespace Verification.GraphVertexCoordinates

open Classical
open Verification.GraphCover Verification.GraphSimplexChains Verification.EvenDifferential
  Verification.IncidenceSaturation

variable {R V : Type*} [CommRing R] [Fintype V] [LinearOrder V]
  (G : SimpleGraph V) (T : Finset V)

/-- Original vertices of the induced complex. -/
abbrev Vertex := {v : V // v ∈ T}

def singletonSimplex (v : Vertex T) : Simplex G T :=
  ⟨{v.val},by simp [v.property],by
    intro a ha b hb hab
    have ha' : a=v.val := by simpa using ha
    have hb' : b=v.val := by simpa using hb
    exact (hab (ha'.trans hb'.symm)).elim⟩

omit [Fintype V] [LinearOrder V] in
theorem singletonSimplex_injective : Function.Injective (singletonSimplex G T) := by
  intro v w h
  apply Subtype.ext
  exact Finset.singleton_injective (congrArg Subtype.val h)

noncomputable def vertexEmbedding : (Vertex T →₀ R) →ₗ[R] (Simplex G T →₀ R) :=
  Finsupp.lmapDomain R R (singletonSimplex G T)

noncomputable def vertexProjection : (Simplex G T →₀ R) →ₗ[R] (Vertex T →₀ R) :=
  Finsupp.lcomapDomain (singletonSimplex G T) (singletonSimplex_injective G T)

omit [Fintype V] [LinearOrder V] in
theorem vertexProjection_apply (x : Simplex G T →₀ R) (v : Vertex T) :
    vertexProjection G T x v=x (singletonSimplex G T v) := rfl

omit [Fintype V] [LinearOrder V] in
theorem vertexProjection_embedding (x : Vertex T →₀ R) :
    vertexProjection G T (vertexEmbedding G T x)=x := by
  ext v
  exact Finsupp.mapDomain_apply (singletonSimplex_injective G T) x v

omit [Fintype V] [LinearOrder V] in
theorem vertexEmbedding_single (v : Vertex T) (r : R) :
    vertexEmbedding G T (Finsupp.single v r)=Finsupp.single (singletonSimplex G T v) r :=
  Finsupp.mapDomain_single

omit [Fintype V] [LinearOrder V] in
theorem vertexProjection_single (v : Vertex T) (r : R) :
    vertexProjection G T (Finsupp.single (singletonSimplex G T v) r)=Finsupp.single v r :=
  Finsupp.comapDomain_single _ _ _ _

/-- The oriented one-skeleton of the induced independence complex. -/
def edgeRelation (v w : Vertex T) : Prop := v.val < w.val ∧ ¬G.Adj v.val w.val

def pairSimplex (v w : Vertex T) (h : edgeRelation G T v w) : Simplex G T :=
  ⟨{v.val,w.val},by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact v.property
    · exact (Finset.mem_singleton.mp hx) ▸ w.property,by
    intro a ha b hb hab
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact h.2
    · exact fun hn => h.2 hn.symm
    · exact (hab rfl).elim⟩

omit [Fintype V] in
/-- The actual two-vertex boundary has its usual ordered sign. -/
theorem pair_boundary (v w : Vertex T) (h : edgeRelation G T v w) :
    basisBoundary (R := R) G T (pairSimplex G T v w h)=
      Finsupp.single (singletonSimplex G T w) 1-
        Finsupp.single (singletonSimplex G T v) 1 := by
  have hne : v.val ≠ w.val := ne_of_lt h.1
  have hnv : ¬w.val < v.val := not_lt_of_ge (le_of_lt h.1)
  have he₁ : eraseSimplex G T (pairSimplex G T v w h) v.val=singletonSimplex G T w := by
    apply Subtype.ext
    simp [eraseSimplex,pairSimplex,singletonSimplex,hne,hne.symm,Finset.erase_insert,Finset.erase_insert_of_ne]
  have he₂ : eraseSimplex G T (pairSimplex G T v w h) w.val=singletonSimplex G T v := by
    apply Subtype.ext
    simp [eraseSimplex,pairSimplex,singletonSimplex,hne,hne.symm,Finset.erase_insert,Finset.erase_insert_of_ne]
  have hr₁ : rankBelow (pairSimplex G T v w h).val v.val=0 := by
    simp [rankBelow,pairSimplex,Finset.filter_insert,Finset.filter_singleton,hnv]
  have hr₂ : rankBelow (pairSimplex G T v w h).val w.val=1 := by
    simp [rankBelow,pairSimplex,Finset.filter_insert,Finset.filter_singleton,h.1]
  simp only [basisBoundary,pairSimplex,Finset.sum_insert (Finset.not_mem_singleton.mpr hne),
    Finset.sum_singleton]
  change Finsupp.single (eraseSimplex G T (pairSimplex G T v w h) v.val)
      ((-1 : R)^rankBelow (pairSimplex G T v w h).val v.val)+
    Finsupp.single (eraseSimplex G T (pairSimplex G T v w h) w.val)
      ((-1 : R)^rankBelow (pairSimplex G T v w h).val w.val)=_
  rw [he₁,he₂,hr₁,hr₂,pow_zero,pow_one,Finsupp.single_neg,sub_eq_add_neg]

omit [Fintype V] [LinearOrder V] in
/-- The vertex coordinates recover exactly every one-vertex chain. -/
theorem vertexEmbedding_projection (x : Simplex G T →₀ R)
    (hx : ∀ J, J.val.card ≠ 1 → x J=0) :
    vertexEmbedding G T (vertexProjection G T x)=x := by
  ext J
  by_cases h : J.val.card=1
  · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp h
    have hvT : v ∈ T := J.property.1 (by simp [hv])
    have hJ : J=singletonSimplex G T ⟨v,hvT⟩ := Subtype.ext hv
    subst J
    exact Finsupp.mapDomain_apply (singletonSimplex_injective G T) _ ⟨v,hvT⟩
  · rw [hx J h]
    apply Finsupp.mapDomain_notin_range
    rintro ⟨v,hv⟩
    apply h
    rw [←hv]
    simp [singletonSimplex]

omit [Fintype V] in
/-- Any actual two-vertex independent set can be ordered to give one oriented edge. -/
theorem pairSimplex_surjective (J : Simplex G T) (hJ : J.val.card=2) :
    ∃ (v w : Vertex T) (h : edgeRelation G T v w), J=pairSimplex G T v w h := by
  obtain ⟨a,b,hab,hval⟩ := Finset.card_eq_two.mp hJ
  have haT : a ∈ T := J.property.1 (by simp [hval])
  have hbT : b ∈ T := J.property.1 (by simp [hval])
  have hn : ¬G.Adj a b := J.property.2 (by simp [hval]) (by simp [hval]) hab
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨⟨a,haT⟩,⟨b,hbT⟩,⟨h,hn⟩,Subtype.ext hval⟩
  · refine ⟨⟨b,hbT⟩,⟨a,haT⟩,⟨h,fun hh => hn hh.symm⟩,?_⟩
    apply Subtype.ext
    simpa only [pairSimplex,Finset.pair_comm] using hval

omit [Fintype V] in
/-- Projecting every actual boundary to vertices gives a sum of signed edges. -/
theorem vertexProjection_basisBoundary_mem (J : Simplex G T) :
    vertexProjection G T (basisBoundary (R := R) G T J) ∈ edgeSpan (edgeRelation G T) := by
  by_cases hJ : J.val.card=2
  · obtain ⟨v,w,h,rfl⟩ := pairSimplex_surjective G T J hJ
    rw [pair_boundary,map_sub,vertexProjection_single,vertexProjection_single]
    have hh : Finsupp.single v (1 : R)-Finsupp.single w 1 ∈ edgeSpan (edgeRelation G T) :=
      Submodule.subset_span ⟨v,w,h,rfl⟩
    simpa only [neg_sub] using (edgeSpan (R := R) (edgeRelation G T)).neg_mem hh
  · have hz : vertexProjection G T (basisBoundary (R := R) G T J)=0 := by
      ext v
      rw [vertexProjection_apply,Finsupp.zero_apply]
      apply basisBoundary_degree G T J (singletonSimplex G T v)
      simpa only [singletonSimplex,Finset.card_singleton] using (Ne.symm hJ)
    rw [hz]
    exact Submodule.zero_mem _

omit [Fintype V] in
/-- This holds for arbitrary finite-support chains, with no cycle assumption. -/
theorem vertexProjection_boundary_mem (x : Simplex G T →₀ R) :
    vertexProjection G T (boundary G T x) ∈ edgeSpan (edgeRelation G T) := by
  induction x using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using (edgeSpan (R := R) (edgeRelation G T)).zero_mem
  | add x y hx hy => simpa only [map_add] using (edgeSpan (R := R) (edgeRelation G T)).add_mem hx hy
  | single J a =>
    simpa only [boundary,Finsupp.linearCombination_single,map_smul] using
      (edgeSpan (R := R) (edgeRelation G T)).smul_mem a (vertexProjection_basisBoundary_mem G T J)

omit [Fintype V] in
/-- Conversely each edge relation is an actual boundary, so the whole span lifts. -/
theorem edgeSpan_lift (x : Vertex T →₀ R) (hx : x ∈ edgeSpan (edgeRelation G T)) :
    ∃ y : Simplex G T →₀ R, boundary G T y=vertexEmbedding G T x := by
  have hl : edgeSpan (R := R) (edgeRelation G T) ≤
      (LinearMap.range (boundary G T)).comap (vertexEmbedding G T) := by
    apply Submodule.span_le.mpr
    rintro x ⟨v,w,h,rfl⟩
    refine ⟨-Finsupp.single (pairSimplex G T v w h) 1,?_⟩
    simp only [map_neg,boundary,Finsupp.linearCombination_single,one_smul,
      pair_boundary,map_sub,vertexEmbedding_single,neg_sub]
  exact hl hx

#print axioms vertexEmbedding_projection
#print axioms pairSimplex_surjective
#print axioms vertexProjection_basisBoundary_mem
#print axioms vertexProjection_boundary_mem
#print axioms edgeSpan_lift
#print axioms Vertex
#print axioms singletonSimplex
#print axioms singletonSimplex_injective
#print axioms vertexEmbedding
#print axioms vertexProjection
#print axioms vertexProjection_apply
#print axioms vertexProjection_embedding
#print axioms vertexEmbedding_single
#print axioms vertexProjection_single
#print axioms edgeRelation
#print axioms pairSimplex
#print axioms pair_boundary

end Verification.GraphVertexCoordinates
