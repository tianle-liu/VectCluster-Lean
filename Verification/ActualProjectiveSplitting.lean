/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Actual Projective Splitting

The original repeated-splitting argument is stated for genuine finite
projective modules, with their actual rank at every prime. The cited
splitting theorem supplies the individual rank-lowering isomorphisms;
Picard and rank-zero vanishing supply the two base cases.
-/
noncomputable section
namespace Verification.ActualProjectiveSplitting
variable (R : Type) [CommRing R]

structure Bundle where
  object : ModuleCat.{0} R
  finite : Module.Finite R object
  projective : Module.Projective R object

variable {R}

def HasRank (P : Bundle R) (r : ℕ) : Prop :=
  ∀ p : PrimeSpectrum R,Module.rankAtStalk P.object p=r

def Trivial (P : Bundle R) : Prop := Module.Free R P.object

/-- This is the rank-lowering conclusion of the cited splitting theorem,
not its iterated conclusion that the original module is free. -/
def SplitsAboveOne : Prop := ∀ (r : ℕ) (P : Bundle R),HasRank P (r+2) →
  ∃ Q : Bundle R,HasRank Q (r+1) ∧ Nonempty (P.object ≃ₗ[R] (Q.object × R))

theorem free_of_splitting (hzero : ∀ P : Bundle R,HasRank P 0 → Trivial P)
    (hline : ∀ P : Bundle R,HasRank P 1 → Trivial P) (hsplit : SplitsAboveOne (R := R))
    (r : ℕ) (P : Bundle R) (hr : HasRank P r) : Trivial P := by
  induction r using Nat.twoStepInduction generalizing P with
  | zero => exact hzero P hr
  | one => exact hline P hr
  | more r _ ih =>
    obtain ⟨Q,hQ,⟨e⟩⟩ := hsplit r P hr
    letI : Module.Free R Q.object := ih Q hQ
    exact Module.Free.of_equiv e.symm

/-- A decomposition of a rank-two bundle into two line bundles. -/
def Decomposable (P : Bundle R) : Prop := ∃ L N : Bundle R,
  HasRank L 1 ∧ HasRank N 1 ∧ Nonempty (P.object ≃ₗ[R] (L.object × N.object))

theorem decomposable_trivial (hline : ∀ P : Bundle R,HasRank P 1 → Trivial P)
    (P : Bundle R) (hP : Decomposable P) : Trivial P := by
  obtain ⟨L,N,hL,hN,⟨e⟩⟩ := hP
  letI : Module.Free R L.object := hline L hL
  letI : Module.Free R N.object := hline N hN
  exact Module.Free.of_equiv e.symm

theorem nontrivial_indecomposable (hline : ∀ P : Bundle R,HasRank P 1 → Trivial P)
    (P : Bundle R) (hP : ¬ Trivial P) : ¬ Decomposable P :=
  fun hd => hP (decomposable_trivial hline P hd)

#print axioms Bundle
#print axioms HasRank
#print axioms Trivial
#print axioms SplitsAboveOne
#print axioms free_of_splitting
#print axioms Decomposable
#print axioms decomposable_trivial
#print axioms nontrivial_indecomposable
end Verification.ActualProjectiveSplitting
