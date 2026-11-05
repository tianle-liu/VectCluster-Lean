/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualEulerOrbits

/-!
# Actual Euler Nontrivial

A nonzero realized Euler class gives an actual nonfree finite
projective module. Picard vanishing rules out a decomposition into lines;
a separately proved rank-three cancellation result supplies one-line
stabilization.
-/
noncomputable section
namespace Verification.ActualEulerNontrivial
open Verification.ActualProjectiveSplitting Verification.ActualOrientations
variable {R : Type} {H : Type*} [CommRing R] [Zero H]
variable (E : Classes (R := R) (r := 2) ≃ H)
variable (hzero : ∀ P : Oriented R 2,Trivial P.bundle → ActualEulerOrbits.classifier E P=0)
variable (hline : ∀ P : Bundle R,HasRank P 1 → Trivial P)

include hzero hline in
theorem realized_indecomposable (x : H) (hx : x≠0) :
    ∃ P : Oriented R 2,ActualEulerOrbits.classifier E P=x ∧
      ¬ Trivial P.bundle ∧ ¬ Decomposable P.bundle := by
  obtain ⟨P,hP⟩ := ActualEulerOrbits.classifier_surjective E x
  have hn : ¬ Trivial P.bundle := fun hf => hx (hP.symm.trans (hzero P hf))
  exact ⟨P,hP,hn,nontrivial_indecomposable hline P.bundle hn⟩

include hzero hline in
theorem one_line_stable_example
    (hstable : ∀ P : Oriented R 2,Nonempty ((P.bundle.object × R) ≃ₗ[R] (Fin 3 → R)))
    (x : H) (hx : x≠0) :
    ∃ P : Oriented R 2,¬ Decomposable P.bundle ∧ ¬ Trivial P.bundle ∧
      Nonempty ((P.bundle.object × R) ≃ₗ[R] (Fin 3 → R)) := by
  obtain ⟨P,_,hn,hi⟩ := realized_indecomposable E hzero hline x hx
  exact ⟨P,hi,hn,hstable P⟩

#print axioms realized_indecomposable
#print axioms one_line_stable_example
end Verification.ActualEulerNontrivial
