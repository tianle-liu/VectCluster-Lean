/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Single Graded Filtration

A finite separated filtration with only one nonzero associated graded
piece gives an actual isomorphism to that piece, without choosing a splitting.
-/
noncomputable section
namespace Verification.SingleGradedFiltration
open CategoryTheory CategoryTheory.Limits
universe u v
variable (C : Type u) [Category.{v} C] [Abelian C]

structure Data where
  F : ℕ → C
  G : ℕ → C
  inclusion : ∀ p,F (p+1) ⟶ F p
  quotient : ∀ p,F p ⟶ G p
  zero : ∀ p,inclusion p ≫ quotient p=0
  exact : ∀ p,(ShortComplex.mk (inclusion p) (quotient p) (zero p)).ShortExact

variable {C} (D : Data C)

abbrev step (p : ℕ) : ShortComplex C := ShortComplex.mk (D.inclusion p) (D.quotient p) (D.zero p)

def stepIso (p : ℕ) (hp : IsZero (D.G p)) : D.F (p+1) ≅ D.F p := by
  haveI : IsIso (D.inclusion p) := (D.exact p).isIso_f_iff.mpr hp
  exact asIso (D.inclusion p)

def initialIso : ∀ q : ℕ,(∀ p,p<q → IsZero (D.G p)) → (D.F 0 ≅ D.F q)
  | 0,_ => Iso.refl _
  | q+1,h => initialIso q (fun p hp => h p (by omega)) ≪≫ (stepIso D q (h q (by omega))).symm

include D in
theorem zero_from (m p : ℕ) (hfinal : IsZero (D.F (p+m)))
    (hG : ∀ k,p≤k → k<p+m → IsZero (D.G k)) : IsZero (D.F p) := by
  induction m generalizing p with
  | zero => simpa only [Nat.add_zero] using hfinal
  | succ m ih =>
    have ht : IsZero (D.F ((p+1)+m)) := by simpa only [Nat.add_assoc,Nat.add_comm 1 m] using hfinal
    have hn := ih (p+1) ht (fun k hk hk' => hG k (by omega) (by omega))
    exact IsZero.of_iso hn (stepIso D p (hG p (by omega) (by omega))).symm

def quotientIso (p : ℕ) (hp : IsZero (D.F (p+1))) : D.F p ≅ D.G p := by
  haveI : IsIso (D.quotient p) := (D.exact p).isIso_g_iff.mpr hp
  exact asIso (D.quotient p)

def singleIso (q m : ℕ) (hfinal : IsZero (D.F (q+1+m)))
    (hG : ∀ p,p≠q → IsZero (D.G p)) : D.F 0 ≅ D.G q :=
  initialIso D q (fun p hp => hG p (by omega)) ≪≫
    quotientIso D q (zero_from D m (q+1) hfinal (fun k hk _ => hG k (by omega)))

#print axioms Data
#print axioms step
#print axioms stepIso
#print axioms initialIso
#print axioms zero_from
#print axioms quotientIso
#print axioms singleIso
end Verification.SingleGradedFiltration
