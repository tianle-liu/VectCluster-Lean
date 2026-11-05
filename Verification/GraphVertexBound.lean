/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphCoverCancellation
import Verification.GraphBalancedCover

/-!
# Graph Vertex Bound

The 2p vertex lower bound for actual reduced independence homology, obtained
from the explicit balanced-cover cancellation. No deletion/link exact sequence,
acyclic matching theorem, or vertex lower-bound hypothesis is used.
-/

namespace Verification.GraphVertexBound

open Classical CategoryTheory CategoryTheory.Limits
open Verification.GraphCover Verification.GraphCoverOrder
  Verification.GraphCoverGrading Verification.GraphCoverProjection
  Verification.GraphCoverCancellation Verification.GraphBalancedCover

variable {R V : Type*} [CommRing R] [Fintype V] [baseOrder : LinearOrder V]
  (G : SimpleGraph V) (T : Finset V)

/-- A surviving degree-p augmented-chain generator requires at least 2p vertices. -/
theorem survivor_vertex_bound (p : ℕ)
    (J : SurvivorIndex G (balancedCover G T) T (-(p : ℤ))) : 2*p ≤ T.card := by
  have hc := survivor_twice_card G T J.val J.property.1
  have hd := J.property.2
  simp only [degree] at hd
  have he : J.val.val.card = p := by omega
  simpa only [he] using hc

/-- With any cover-first ordering, the original graph complex has zero reduced
homology in degree p-1 when there are fewer than 2p vertices. -/
theorem homology_zero_of_small_vertices (hord : CoverOrdered (balancedCover G T))
    (p : ℕ) (hp : T.card < 2*p) :
    IsZero ((graphComplex (R := R) G (balancedCover G T) T
      (balancedCover_covers G T) hord).homology (-(p : ℤ))) := by
  apply graphHomology_zero_of_no_survivors
  intro J
  have h := survivor_vertex_bound G T p J
  omega

/-- The requested 2p lower bound, for categorical homology of the actual deletion complex. -/
theorem nonzero_homology_vertex_bound (hord : CoverOrdered (balancedCover G T))
    (p : ℕ)
    (h : ¬ IsZero ((graphComplex (R := R) G (balancedCover G T) T
      (balancedCover_covers G T) hord).homology (-(p : ℤ)))) : 2*p ≤ T.card := by
  by_contra hle
  exact h (homology_zero_of_small_vertices G T hord p (by omega))

/-- A specific finite order with the selected cover first; there is no ordering
existence assumption in the resulting graph complex. -/
noncomputable def canonicalGraphComplex : CochainComplex (ModuleCat R) ℤ := by
  let C0 := balancedCover G T
  have hc : Covers G C0 := balancedCover_covers G T
  let o : LinearOrder V := @coverOrder V baseOrder C0
  have ho : @CoverOrdered V o C0 := @coverOrder_property V baseOrder C0
  letI : LinearOrder V := o
  exact graphComplex G C0 T hc ho

/-- Unconditional finite-vertex lower bound for a specified actual augmented chain model. -/
theorem canonical_nonzero_homology_vertex_bound (p : ℕ)
    (h : ¬ IsZero ((canonicalGraphComplex (R := R) G T).homology (-(p : ℤ)))) :
    2*p ≤ T.card := by
  let C0 := balancedCover G T
  have hc : Covers G C0 := balancedCover_covers G T
  let o : LinearOrder V := @coverOrder V baseOrder C0
  have ho : @CoverOrdered V o C0 := @coverOrder_property V baseOrder C0
  letI : LinearOrder V := o
  by_contra hle
  apply h
  change IsZero ((graphComplex (R := R) G C0 T hc ho).homology (-(p : ℤ)))
  apply graphHomology_zero_of_no_survivors
  intro J
  have hs : @Survives V baseOrder.toDecidableEq G C0 T J.val := by
    have changeDec : ∀ d e : DecidableEq V,
        @Survives V d G C0 T J.val → @Survives V e G C0 T J.val := by
      intro d e hs
      have he : d=e := Subsingleton.elim _ _
      subst e
      exact hs
    exact changeDec _ _ J.property.1
  have hb := @survivor_twice_card V _ baseOrder.toDecidableEq G T J.val hs
  have hd := J.property.2
  simp only [degree] at hd
  omega

#print axioms survivor_vertex_bound
#print axioms homology_zero_of_small_vertices
#print axioms nonzero_homology_vertex_bound
#print axioms canonicalGraphComplex
#print axioms canonical_nonzero_homology_vertex_bound

end Verification.GraphVertexBound
