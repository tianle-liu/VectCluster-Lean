/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalSignComplex
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Original Mutable Graph

The original order-free anticliques and their maximum are exactly
independent sets and the independence number of the actual mutable graph.
-/
noncomputable section
namespace Verification.OriginalMutableGraph
open ExchangeReindex
variable {V C : Type} (B : (V ⊕ C) → V → ℤ)

def graph : SimpleGraph V where
  Adj a i := a≠i ∧ (B (Sum.inl a) i≠0 ∨ B (Sum.inl i) a≠0)
  symm := fun _ _ hi => ⟨hi.1.symm,hi.2.symm⟩
  loopless := fun _ hi => hi.1 rfl

theorem independent_iff (I : Finset V) :
    (graph B).IsIndepSet (I : Set V) ↔ PrincipalIndependent B I := by
  constructor
  · intro hi a ha i hi' hne
    by_contra hn
    exact hi ha hi' hne ⟨hne,Or.inl hn⟩
  · intro hi a ha i hi' hne hadj
    rcases hadj.2 with hn | hn
    · exact hn (hi a ha i hi' hne)
    · exact hn (hi i hi' a ha hne.symm)

variable [Fintype V]

theorem alpha_eq : OriginalSignComplex.alpha B=(graph B).indepNum := by
  apply le_antisymm
  · apply (IndependentFamilyBound.maximum_le_iff _ _).mpr
    intro I hI
    exact ((independent_iff B I).mpr hI).card_le_indepNum
  · obtain ⟨I,hI⟩ := (graph B).exists_isNIndepSet_indepNum
    have hi := OriginalSignComplex.card_le_alpha B I ((independent_iff B I).mp hI.1)
    simpa only [hI.2] using hi

#print axioms graph
#print axioms independent_iff
#print axioms alpha_eq
end Verification.OriginalMutableGraph
