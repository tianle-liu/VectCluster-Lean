/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.Clique
import Verification.FreezingLattice
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Powerset

/-!
# Clique Saturation

The article's clique-coefficient AS assertion, including deficient-rank
full matrices. For each actual independent set, delete its mutable rows,
restrict its columns, and construct the retained frozen-row retraction.
-/
namespace Verification.CliqueSaturation
open Verification.FreezingLattice

variable {R P M : Type*} [CommRing R] [AddCommGroup P] [AddCommGroup M]
  [Module R P] [Module R M] [NoZeroSMulDivisors R M]

theorem split_range_saturated (f : P →ₗ[R] M) (r : M →ₗ[R] P)
    (hr : Function.LeftInverse r f) : Saturated (LinearMap.range f) := by
  intro a ha x hx
  obtain ⟨p,hp⟩ := hx
  have hp' : p = a • r x := by
    have h := congrArg r hp
    simpa only [hr p, map_smul] using h
  have hcancel : a • (f (r x) - x) = 0 := by
    rw [smul_sub, ← map_smul, ← hp', hp, sub_self]
  have heq : f (r x) = x := sub_eq_zero.mp ((smul_eq_zero.mp hcancel).resolve_left ha)
  exact ⟨r x,heq⟩

variable {V C : Type*} [DecidableEq C]

/-- Each color class is a clique of the original graph. -/
def CliquePartition (G : SimpleGraph V) (c : V → C) : Prop :=
  ∀ ⦃v w⦄, v ≠ w → c v = c w → G.Adj v w

omit [DecidableEq C] in
theorem independent_colors_injective (G : SimpleGraph V) (c : V → C)
    (hc : CliquePartition G c) (I : Finset V) (hI : G.IsIndepSet (I : Set V)) :
    Function.Injective (fun i : I => c i) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  exact hI i.property j.property hne (hc hne hij)

noncomputable def anticliqueMatrix (B : V → V → ℤ) (c : V → C) (I : Finset V) :
    Matrix ({v : V // v ∉ I} ⊕ C) I ℤ :=
  Verification.Clique.extendedMatrix (fun a i => B a i) (fun i : I => c i)

noncomputable def anticliqueRetraction (c : V → C) (I : Finset V) :
    (({v : V // v ∉ I} ⊕ C) → ℤ) →ₗ[ℤ] (I → ℤ) :=
  Verification.Clique.extendedRetraction (fun i : I => c i)

theorem anticlique_split (G : SimpleGraph V) (B : V → V → ℤ) (c : V → C)
    (hc : CliquePartition G c) (I : Finset V) (hI : G.IsIndepSet (I : Set V)) :
    Function.LeftInverse (anticliqueRetraction c I) (anticliqueMatrix B c I).mulVecLin :=
  Verification.Clique.extended_left_inverse _ _ (independent_colors_injective G c hc I hI)

theorem anticlique_rank_and_saturation (G : SimpleGraph V) (B : V → V → ℤ) (c : V → C)
    (hc : CliquePartition G c) (I : Finset V) (hI : G.IsIndepSet (I : Set V)) :
    Function.Injective (anticliqueMatrix B c I).mulVecLin ∧
      Saturated (LinearMap.range (anticliqueMatrix B c I).mulVecLin) :=
  ⟨(anticlique_split G B c hc I hI).injective,
    split_range_saturated _ _ (anticlique_split G B c hc I hI)⟩

#print axioms split_range_saturated
#print axioms CliquePartition
#print axioms independent_colors_injective
#print axioms anticliqueMatrix
#print axioms anticliqueRetraction
#print axioms anticlique_split
#print axioms anticlique_rank_and_saturation
end Verification.CliqueSaturation
