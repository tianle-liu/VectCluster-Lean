/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FundamentalIdealCohomologyInput

/-!
# Fundamental Ideal Chow Comparison

Positive Chow vanishing forces the actual coefficient morphism
H^p(I^p)→H^p(W) to be bijective. The proof iterates the ordinary Milnor
long exact sequences and treats degree one by the actual rank-parity map.
It does not identify either group with a proxy lattice or complex.
-/
noncomputable section
namespace Verification.FundamentalIdealChowComparison
open CategoryTheory AlgebraicGeometry
variable {M : Type*} (T : StrictNisnevichInput.Theory M)
variable (k : Type) [Field k] [PerfectField k] (h2 : (2 : k) ≠ 0)
variable (IP KM : ℕ → M) (W : M)
variable (Q : FundamentalIdealCohomologyInput.Theory T k IP KM W)
variable (CH : Scheme → ℕ → AddCommGrp)
variable (S : FundamentalIdealCohomologyInput.Standard T k IP KM W Q CH h2)
variable (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R]
local notation "X" => Spec (CommRingCat.of R)

include S in
theorem diagonal_zero (j : ℕ) (hCH : Subsingleton (CH X j)) :
    Subsingleton (T.cohomology X (KM j) j) := by
  letI := hCH
  letI : Subsingleton (ChowWittFiberProductInput.modTwo (CH X j)) :=
    (QuotientAddGroup.mk'_surjective (ChowWittFiberProductInput.doubling (CH X j)).range).subsingleton
  let e := (S.diagonal R j).some
  exact ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩

include S in
theorem inclusion_bijective (p : ℕ) (hp : 0 < p)
    (hCH : ∀ q : ℕ, 0 < q → q < p → Subsingleton (CH X q))
    (j : ℕ) (hj : j < p) : Function.Bijective (Q.inclusion R j p) := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hright : Q.quotient R j (q+1) = 0 := by
    letI := S.above R j (q+1) hj
    ext a
    exact Subsingleton.elim _ _
  have hleft : Q.connecting R j q = 0 := by
    by_cases hq : q = 0
    · subst q
      have hj0 : j = 0 := by omega
      subst j
      exact ExactCoefficientComparison.connecting_zero_of_surjective
        (Q.quotient R 0 0) (Q.connecting R 0 0) (S.left_exact R 0 0) (S.parity R)
    · have hzero : Subsingleton (T.cohomology X (KM j) q) := by
        by_cases he : j = q
        · subst j
          exact diagonal_zero T k h2 IP KM W Q CH S R q (hCH q (by omega) (by omega))
        · exact S.above R j q (by omega)
      ext a
      have ha : a = 0 := hzero.elim _ _
      rw [ha,map_zero]
      rfl
  exact ExactCoefficientComparison.bijective_of_zero_ends
    (Q.connecting R j q) (Q.inclusion R j (q+1)) (Q.quotient R j (q+1))
      (S.middle_exact R j q) (S.right_exact R j (q+1)) hleft hright

include S in
theorem toW_bijective (p : ℕ) (hp : 0 < p)
    (hCH : ∀ q : ℕ, 0 < q → q < p → Subsingleton (CH X q)) :
    Function.Bijective (Q.toW R p p) := by
  have h (j : ℕ) : j ≤ p → Function.Bijective (Q.toW R j p) := by
    induction j with
    | zero => intro _; exact S.zero_bijective R p
    | succ j ih =>
      intro hj
      rw [S.inclusion_toW R j p]
      exact (ih (by omega)).comp
        (inclusion_bijective T k h2 IP KM W Q CH S R p hp hCH j (by omega))
  exact h p le_rfl

def toWEquiv (p : ℕ) (hp : 0 < p)
    (hCH : ∀ q : ℕ, 0 < q → q < p → Subsingleton (CH X q)) :
    T.cohomology X (IP p) p ≃+ T.cohomology X W p :=
  AddEquiv.ofBijective (Q.toW R p p) (toW_bijective T k h2 IP KM W Q CH S R p hp hCH)

theorem toWEquiv_apply (p : ℕ) (hp : 0 < p)
    (hCH : ∀ q : ℕ, 0 < q → q < p → Subsingleton (CH X q))
    (a : T.cohomology X (IP p) p) :
    toWEquiv T k h2 IP KM W Q CH S R p hp hCH a = Q.toW R p p a := rfl

#print axioms diagonal_zero
#print axioms inclusion_bijective
#print axioms toW_bijective
#print axioms toWEquiv
#print axioms toWEquiv_apply
end Verification.FundamentalIdealChowComparison
