/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProjectiveRankSum
import Verification.ActualEulerNontrivial

/-!
# Projective Indecomposable

On the domain coordinate rings, a nonfree rank-two projective module
with trivial line bundles has no decomposition into nonzero projective
summands of any ranks. This closes the line-plus-line reduction.
-/
noncomputable section
namespace Verification.ProjectiveIndecomposable
open Verification.ActualProjectiveSplitting Verification.ActualOrientations
variable {R : Type} [CommRing R] [IsDomain R]

def Indecomposable (P : Bundle R) : Prop := ∀ (Q N : Bundle R),
  Nonempty (P.object ≃ₗ[R] (Q.object × N.object)) → Subsingleton Q.object ∨ Subsingleton N.object

theorem of_nonfree_rank_two (hline : ∀ P : Bundle R,HasRank P 1 → Trivial P)
    (P : Bundle R) (hr : HasRank P 2) (hn : ¬ Trivial P) : Indecomposable P := by
  intro Q N he
  obtain ⟨q,hQ⟩ := ProjectiveConstantRank.exists_rank Q
  obtain ⟨n,hN⟩ := ProjectiveConstantRank.exists_rank N
  by_cases hq : q=0
  · exact Or.inl (ProjectiveZeroRank.subsingleton Q (hq ▸ hQ))
  by_cases hn' : n=0
  · exact Or.inr (ProjectiveZeroRank.subsingleton N (hn' ▸ hN))
  have hs := ProjectiveRankSum.rank_numbers he.some hr hQ hN
  have hq1 : q=1 := by omega
  have hn1 : n=1 := by omega
  exact (hn (decomposable_trivial hline P ⟨Q,N,hq1 ▸ hQ,hn1 ▸ hN,he⟩)).elim

variable {H : Type*} [Zero H] (E : Classes (R := R) (r := 2) ≃ H)
variable (hzero : ∀ P : Oriented R 2,Trivial P.bundle → ActualEulerOrbits.classifier E P=0)
variable (hline : ∀ P : Bundle R,HasRank P 1 → Trivial P)

include hzero hline in
theorem nonzero_euler (x : H) (hx : x≠0) : ∃ P : Oriented R 2,
    ActualEulerOrbits.classifier E P=x ∧ ¬ Trivial P.bundle ∧ Indecomposable P.bundle := by
  obtain ⟨P,hP,hn,_⟩ := ActualEulerNontrivial.realized_indecomposable E hzero hline x hx
  exact ⟨P,hP,hn,of_nonfree_rank_two hline P.bundle P.rank hn⟩

include hzero hline in
theorem one_line_example
    (hstable : ∀ P : Oriented R 2,Nonempty ((P.bundle.object × R) ≃ₗ[R] (Fin 3 → R)))
    (x : H) (hx : x≠0) : ∃ P : Oriented R 2,Indecomposable P.bundle ∧ ¬ Trivial P.bundle ∧
      Nonempty ((P.bundle.object × R) ≃ₗ[R] (Fin 3 → R)) := by
  obtain ⟨P,_,hn,hi⟩ := nonzero_euler E hzero hline x hx
  exact ⟨P,hi,hn,hstable P⟩

#print axioms Indecomposable
#print axioms of_nonfree_rank_two
#print axioms nonzero_euler
#print axioms one_line_example
end Verification.ProjectiveIndecomposable
