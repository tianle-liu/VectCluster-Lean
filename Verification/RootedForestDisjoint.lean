/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RootedForestCertificate

/-!
# Rooted Forest Disjoint

Adjacency in disjoint unions of rooted forests. Vertices in one component have
the original adjacency relation, and vertices in distinct components are not adjacent.
-/
namespace Verification.RootedForestDisjoint
open Verification.RootedForestCertificate
variable {S : Type*} {K : S→Type*} (P : ∀s,Forest (K s))
theorem same_adj (s : S) (i j : K s) :
    (Forest.disjoint P).Adj ⟨s,i⟩ ⟨s,j⟩ ↔ (P s).Adj i j := by
  simp [Forest.Adj,Forest.disjoint,Option.map_eq_some_iff]
theorem different_adj (s t : S) (h : s≠t) (i : K s) (j : K t) :
    ¬(Forest.disjoint P).Adj ⟨s,i⟩ ⟨t,j⟩ := by
  rintro (hh|hh)
  · obtain ⟨x,_,he⟩ := Option.map_eq_some_iff.mp hh
    exact h (congrArg Sigma.fst he)
  · obtain ⟨x,_,he⟩ := Option.map_eq_some_iff.mp hh
    exact h (congrArg Sigma.fst he).symm
#print axioms same_adj
#print axioms different_adj
end Verification.RootedForestDisjoint
