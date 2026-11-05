/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphVertexCoordinates

/-!
# Graph Low Boundary

Integral saturation of the actual augmented graph boundaries in cardinality
zero and one, proved with explicit finite-support preimages.
-/

namespace Verification.GraphLowBoundary

open Classical
open Verification.GraphCover Verification.GraphSimplexChains
  Verification.GraphVertexCoordinates Verification.IncidenceSaturation
  Verification.EvenDifferential

variable {R V : Type*} [CommRing R] [IsDomain R] [Fintype V] [LinearOrder V]
  (G : SimpleGraph V) (T : Finset V)

omit [Fintype V] in
/-- Degree-zero reduced cycles have saturated boundaries because their vertex
coordinates are precisely signed edge relations. -/
theorem one_boundary_saturated (a : R) (ha : a ≠ 0) (x : Simplex G T →₀ R)
    (hx : ∀ J, J.val.card ≠ 1 → x J=0)
    (hy : ∃ y, boundary G T y=a • x) : ∃ y, boundary G T y=x := by
  obtain ⟨y,hy⟩ := hy
  have hp := vertexProjection_boundary_mem G T y
  rw [hy,map_smul] at hp
  have hxp := edgeSpan_saturated (edgeRelation G T) a ha _ hp
  obtain ⟨z,hz⟩ := edgeSpan_lift G T _ hxp
  exact ⟨z,hz.trans (vertexEmbedding_projection G T x hx)⟩

/-- The empty independent set, the basis of augmented chain degree -1. -/
def emptySimplex : Simplex G T := ⟨∅,Finset.empty_subset _,by simp⟩

omit [IsDomain R] [Fintype V] in
theorem singleton_boundary (v : Vertex T) :
    basisBoundary (R := R) G T (singletonSimplex G T v)=
      Finsupp.single (emptySimplex G T) 1 := by
  have he : eraseSimplex G T (singletonSimplex G T v) v.val=emptySimplex G T := by
    apply Subtype.ext
    simp [eraseSimplex,singletonSimplex,emptySimplex]
  have hr : rankBelow (singletonSimplex G T v).val v.val=0 := by
    simp [rankBelow,singletonSimplex,Finset.filter_singleton]
  change (∑ i ∈ ({v.val} : Finset V),Finsupp.single
    (eraseSimplex G T (singletonSimplex G T v) i)
    ((-1 : R)^rankBelow (singletonSimplex G T v).val i))=_
  rw [Finset.sum_singleton,he,hr,pow_zero]

omit [IsDomain R] [Fintype V] in
theorem empty_boundary : basisBoundary (R := R) G T (emptySimplex G T)=0 := by
  simp [basisBoundary,emptySimplex]

omit [IsDomain R] [Fintype V] [LinearOrder V] in
theorem empty_chain (x : Simplex G T →₀ R) (hx : ∀ J, J.val.card ≠ 0 → x J=0) :
    x=Finsupp.single (emptySimplex G T) (x (emptySimplex G T)) := by
  ext J
  by_cases hJ : J=emptySimplex G T
  · subst J; simp
  · have hcard : J.val.card ≠ 0 := by
      intro h
      apply hJ
      exact Subtype.ext (Finset.card_eq_zero.mp h)
    rw [hx J hcard,Finsupp.single_eq_of_ne (Ne.symm hJ)]

omit [IsDomain R] [Fintype V] in
theorem boundary_of_empty_vertices (hT : T=∅) (y : Simplex G T →₀ R) : boundary G T y=0 := by
  have hD : boundary (R := R) G T=0 := by
    apply Finsupp.lhom_ext
    intro J a
    have hJ : J=emptySimplex G T := by
      apply Subtype.ext
      exact Finset.eq_empty_iff_forall_not_mem.mpr (fun i hi => by
        have ht := J.property.1 hi
        simp [hT] at ht)
    subst J
    simp only [boundary,Finsupp.linearCombination_single,empty_boundary,smul_zero,
      LinearMap.zero_apply]
  rw [hD,LinearMap.zero_apply]

omit [Fintype V] in
/-- Augmentation boundaries are also saturated, including the empty induced graph. -/
theorem zero_boundary_saturated (a : R) (ha : a ≠ 0) (x : Simplex G T →₀ R)
    (hx : ∀ J, J.val.card ≠ 0 → x J=0)
    (hy : ∃ y, boundary G T y=a • x) : ∃ y, boundary G T y=x := by
  rcases T.eq_empty_or_nonempty with hT | ⟨v,hv⟩
  · obtain ⟨y,hy⟩ := hy
    have hz : a • x=0 := hy.symm.trans (boundary_of_empty_vertices G T hT y)
    have he : x=0 := (eq_zero_or_eq_zero_of_smul_eq_zero hz).resolve_left ha
    exact ⟨0,by rw [map_zero,he]⟩
  · refine ⟨Finsupp.single (singletonSimplex G T ⟨v,hv⟩) (x (emptySimplex G T)),?_⟩
    simp only [boundary,Finsupp.linearCombination_single,singleton_boundary,
      Finsupp.smul_single,smul_eq_mul,mul_one]
    exact (empty_chain G T x hx).symm

#print axioms one_boundary_saturated
#print axioms emptySimplex
#print axioms singleton_boundary
#print axioms empty_boundary
#print axioms empty_chain
#print axioms boundary_of_empty_vertices
#print axioms zero_boundary_saturated

end Verification.GraphLowBoundary
