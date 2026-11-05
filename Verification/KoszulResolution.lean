/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.KoszulRecursive
import Verification.ProjectiveRankCriterion
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Lean.Elab.Tactic.Omega

/-!
# Koszul Resolution

The finite free Koszul resolution with its actual augmentation and
regular-sequence exactness, together with the resulting binomial Euler
class in the actual finite-projective Grothendieck group.
-/
noncomputable section
universe u
namespace Verification.KoszulResolution
open Verification.KoszulRecursive Verification.ProjectiveClasses
open Verification.ProjectiveGrothendieck Verification.ProjectiveRankCriterion
open RingTheory.Sequence CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]

theorem supported (l : List R) (p : ℕ) (hp : l.length < p) : Subsingleton (term R l p) := by
  induction l generalizing p with
  | nil => cases p with
    | zero => simp at hp
    | succ p => exact inferInstanceAs (Subsingleton (Fin 0 → R))
  | cons x l ih =>
    cases p with
    | zero => simp at hp
    | succ p =>
      have h : l.length < p := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hp
      letI := ih p h
      letI := ih (p+1) (by omega)
      exact inferInstanceAs (Subsingleton (term R l (p+1) × term R l p))

theorem exactAt (l : List R) (hl : IsWeaklyRegular R l.reverse) (p : ℕ) :
    (complex R l).ExactAt (p+1) := by
  apply ((complex R l).exactAt_iff' (p+1+1) (p+1) p (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range ((complex R l).d (p+1+1) (p+1)).hom =
    LinearMap.ker ((complex R l).d (p+1) p).hom
  simpa only [complex,ChainComplex.of_d,ModuleCat.hom_ofHom] using positive_exact R l hl p

theorem positive_homology_zero (l : List R) (hl : IsWeaklyRegular R l.reverse) (p : ℕ) :
    IsZero ((complex R l).homology (p+1)) := (exactAt R l hl p).isZero_homology

variable [Nontrivial R]

theorem term_rank (l : List R) (p : ℕ) : Module.finrank R (term R l p)=l.length.choose p := by
  induction l generalizing p with
  | nil =>
    cases p with
    | zero => simp [term]
    | succ p => simp [term,positiveTerm,Module.finrank_pi]
  | cons x l ih =>
    cases p with
    | zero => simp [term]
    | succ p =>
      letI := term_free R l p
      letI := term_free R l (p+1)
      letI := term_finite R l p
      letI := term_finite R l (p+1)
      change Module.finrank R (term R l (p+1) × term R l p)=(l.length+1).choose (p+1)
      rw [Module.finrank_prod,ih,ih,Nat.choose_succ_succ]
      exact Nat.add_comm _ _

def freeEquiv (l : List R) (p : ℕ) : term R l p ≃ₗ[R] (Fin (l.length.choose p) → R) := by
  letI := term_free R l p
  letI := term_finite R l p
  exact (Module.finBasisOfFinrankEq R (term R l p) (term_rank R l p)).equivFun

def object (l : List R) (p : ℕ) : Object R := by
  letI := term_free R l p
  letI := term_finite R l p
  exact of R (term R l p)

theorem object_class (l : List R) (p : ℕ) :
    completionClass R (object R l p)=l.length.choose p • unitClass R := by
  have he := congrArg (inclusion R) ((classOf_eq_iff R (object R l p)
    (of R (Fin (l.length.choose p) → R))).mpr ⟨freeEquiv R l p⟩)
  exact he.trans (free_class R _)

def euler (l : List R) : Completion R :=
  ∑ p ∈ Finset.range (l.length+1), ((-1:ℤ)^p) • completionClass R (object R l p)

theorem euler_zero (l : List R) (hl : l ≠ []) : euler R l=0 := by
  have he : euler R l = ∑ p ∈ Finset.range (l.length+1),
      ((-1)^p * l.length.choose p : ℤ) • unitClass R := by
    apply Finset.sum_congr rfl
    intro p _
    rw [object_class]
    simp [mul_smul]
  rw [he]
  exact Verification.StableFree.koszul_class_zero _ (by simpa using hl) _

#print axioms supported
#print axioms exactAt
#print axioms positive_homology_zero
#print axioms term_rank
#print axioms freeEquiv
#print axioms object
#print axioms object_class
#print axioms euler
#print axioms euler_zero
end Verification.KoszulResolution
