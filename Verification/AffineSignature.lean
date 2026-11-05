/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SignatureLattice
import Mathlib.Tactic.Ring
import Mathlib.GroupTheory.OrderOfElement

/-!
# Affine Signature

Affine Boolean-coordinate invariance for the actual integer lattices defined
in `Verification.SignatureLattice`. Boolean affine coordinates are parity sums
of arbitrary sets of input coordinates, optionally complemented by translation.
This file uses only integer function rings and finite Boolean cubes.
-/

namespace Verification.AffineSignature

open Finset Verification.SignatureLattice

variable {α β : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem monomial_union (A B : Finset α) :
    booleanMonomial (A ∪ B) = booleanMonomial A * booleanMonomial B := by
  funext S
  simp only [booleanMonomial, Finset.union_subset_iff, Pi.mul_apply]
  split_ifs <;> simp_all

theorem evaluate_eq_sum (c : Finset α → ℤ) :
    evaluate c = ∑ A : Finset α, c A • booleanMonomial A := by
  funext S
  simp only [evaluate_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro A _
  exact mul_comm _ _

theorem monomial_scalar_mem (s : ℤ) (A : Finset α) (k : ℤ)
    (hk : (2 : ℤ) ^ exponent s A ∣ k) :
    k • booleanMonomial A ∈ signatureLattice s := by
  refine ⟨Pi.single A k, ?_, ?_⟩
  · intro B
    by_cases h : B = A
    · subst B
      simpa using hk
    · simp [Pi.single_apply, h]
  · funext S
    simp [evaluate_apply, Pi.single_apply, mul_ite, mul_comm]

theorem monomial_mem_level (A : Finset α) :
    booleanMonomial A ∈ signatureLattice (A.card : ℤ) := by
  simpa using monomial_scalar_mem (A.card : ℤ) A 1 (by simp [exponent])

omit [Fintype α] in
theorem monomial_product_scalar (A B : Finset α) (a b : ℤ) :
    (a • booleanMonomial A) * (b • booleanMonomial B) =
      (a * b) • booleanMonomial (A ∪ B) := by
  rw [monomial_union]
  funext S
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype α] in
theorem union_exponent_le (r s : ℤ) (A B : Finset α) :
    exponent (r + s) (A ∪ B) ≤ exponent r A + exponent s B := by
  have h := Finset.card_union_le A B
  dsimp [exponent]
  omega

/-- The signature lattices form a multiplicative filtration of the function ring. -/
theorem mul_mem (r s : ℤ) (f g : Finset α → ℤ)
    (hf : f ∈ signatureLattice r) (hg : g ∈ signatureLattice s) :
    f * g ∈ signatureLattice (r + s) := by
  obtain ⟨c, hc, rfl⟩ := hf
  obtain ⟨d, hd, rfl⟩ := hg
  rw [evaluate_eq_sum, evaluate_eq_sum, Finset.sum_mul]
  apply Submodule.sum_mem
  intro A _
  rw [Finset.mul_sum]
  apply Submodule.sum_mem
  intro B _
  rw [monomial_product_scalar]
  apply monomial_scalar_mem
  apply (pow_dvd_pow (2 : ℤ) (union_exponent_le r s A B)).trans
  rw [pow_add]
  exact mul_dvd_mul (hc A) (hd B)

omit [Fintype α] [DecidableEq α] in
theorem shift_exponent_le (r s : ℤ) (A : Finset α) :
    exponent s A ≤ (r - s).toNat + exponent r A := by
  dsimp [exponent]
  omega

/-- Multiplication by the necessary power of two lowers the filtration level. -/
theorem power_smul_mem (r s : ℤ) (f : Finset α → ℤ)
    (hf : f ∈ signatureLattice r) :
    (2 : ℤ) ^ (r - s).toNat • f ∈ signatureLattice s := by
  obtain ⟨c, hc, rfl⟩ := hf
  refine ⟨(2 : ℤ) ^ (r - s).toNat • c, ?_, ?_⟩
  · intro A
    apply (pow_dvd_pow (2 : ℤ) (shift_exponent_le r s A)).trans
    rw [pow_add]
    exact mul_dvd_mul (dvd_refl _) (hc A)
  · exact map_smul evaluate _ c

/-- Constants have degree zero. -/
theorem one_mem_zero : (1 : Finset α → ℤ) ∈ signatureLattice 0 := by
  simpa [booleanMonomial] using monomial_mem_level (∅ : Finset α)

/-- Boolean coordinates have filtration level one. -/
theorem coordinate_mem_one (i : α) :
    booleanMonomial ({i} : Finset α) ∈ signatureLattice 1 := by
  simpa using monomial_mem_level ({i} : Finset α)

theorem one_mem_one : (1 : Finset α → ℤ) ∈ signatureLattice 1 := by
  simpa using power_smul_mem 0 1 (1 : Finset α → ℤ) one_mem_zero

/-- XOR is the integer polynomial x + y - 2xy on Boolean values. -/
def xorFunction (f g : Finset α → ℤ) : Finset α → ℤ := f + g - (2 : ℤ) • (f * g)

theorem xor_mem_one (f g : Finset α → ℤ)
    (hf : f ∈ signatureLattice 1) (hg : g ∈ signatureLattice 1) :
    xorFunction f g ∈ signatureLattice 1 := by
  apply Submodule.sub_mem _ (Submodule.add_mem _ hf hg)
  have h := power_smul_mem 2 1 (f * g) (mul_mem 1 1 f g hf hg)
  simpa using h

/-- The parity of the indicated input bits, as an integer-valued Boolean function. -/
def parityCoordinate (A S : Finset α) : ℤ := ((A ∩ S).card % 2 : ℕ)

omit [Fintype α] in
theorem parityCoordinate_bit (A S : Finset α) :
    parityCoordinate A S = 0 ∨ parityCoordinate A S = 1 := by
  have h := Nat.mod_lt (A ∩ S).card (by decide : 0 < 2)
  dsimp [parityCoordinate]
  omega

omit [Fintype α] in
theorem parityCoordinate_insert (i : α) (A : Finset α) (hi : i ∉ A) :
    parityCoordinate (insert i A) =
      xorFunction (booleanMonomial {i}) (parityCoordinate A) := by
  funext S
  have hnot : i ∉ A ∩ S := by simp [hi]
  by_cases hiS : i ∈ S
  · have hset : insert i A ∩ S = insert i (A ∩ S) := by
      ext x
      by_cases hx : x = i <;> simp_all
    simp only [parityCoordinate, hset, Finset.card_insert_of_not_mem hnot,
      xorFunction, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
      smul_eq_mul, booleanMonomial, Finset.singleton_subset_iff, if_pos hiS]
    omega
  · have hset : insert i A ∩ S = A ∩ S := by
      ext x
      by_cases hx : x = i <;> simp_all
    simp [parityCoordinate, hset, xorFunction, booleanMonomial, hiS]

/-- Every linear Boolean coordinate, with arbitrary support, belongs to Λ₁. -/
theorem parityCoordinate_mem_one (A : Finset α) :
    parityCoordinate A ∈ signatureLattice 1 := by
  induction A using Finset.induction_on with
  | empty =>
      have hzero : parityCoordinate (∅ : Finset α) = 0 := by
        funext S
        simp [parityCoordinate]
      rw [hzero]
      exact Submodule.zero_mem _
  | @insert i A hi ih =>
      rw [parityCoordinate_insert i A hi]
      exact xor_mem_one _ _ (coordinate_mem_one i) ih

/-- A translation complements the corresponding Boolean coordinate. -/
def affineCoordinate (A : Finset α) (b : Bool) : Finset α → ℤ :=
  if b then 1 - parityCoordinate A else parityCoordinate A

omit [Fintype α] in
theorem affineCoordinate_bit (A : Finset α) (b : Bool) (S : Finset α) :
    affineCoordinate A b S = 0 ∨ affineCoordinate A b S = 1 := by
  have h := parityCoordinate_bit A S
  cases b <;> simp only [affineCoordinate, Bool.false_eq_true, ↓reduceIte,
    Pi.sub_apply, Pi.one_apply] <;> omega

theorem affineCoordinate_mem_one (A : Finset α) (b : Bool) :
    affineCoordinate A b ∈ signatureLattice 1 := by
  cases b
  · exact parityCoordinate_mem_one A
  · exact Submodule.sub_mem _ one_mem_one (parityCoordinate_mem_one A)

/-- Pullback along a map of finite Boolean cubes is an integer linear map. -/
def pullback (F : Finset α → Finset β) :
    (Finset β → ℤ) →ₗ[ℤ] (Finset α → ℤ) where
  toFun f S := f (F S)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype α] in
theorem monomial_eq_product (A : Finset α) :
    booleanMonomial A = ∏ i ∈ A, booleanMonomial ({i} : Finset α) := by
  induction A using Finset.induction_on with
  | empty => funext S; simp [booleanMonomial]
  | @insert i A hi ih =>
      rw [Finset.prod_insert hi, ← ih, ← monomial_union]
      rfl

theorem product_mem_level (A : Finset β) (g : β → Finset α → ℤ)
    (hg : ∀ i ∈ A, g i ∈ signatureLattice 1) :
    (∏ i ∈ A, g i) ∈ signatureLattice (A.card : ℤ) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using (one_mem_zero (α := α))
  | @insert i A hi ih =>
      have hgi := hg i (Finset.mem_insert_self _ _)
      have hrest := ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      simpa [Finset.prod_insert hi, Finset.card_insert_of_not_mem hi, add_comm] using
        mul_mem 1 (A.card : ℤ) (g i) (∏ j ∈ A, g j) hgi hrest

variable [Fintype β] [DecidableEq β]

omit [Fintype β] in
theorem pullback_monomial_mem (F : Finset α → Finset β)
    (hF : ∀ i : β, pullback F (booleanMonomial {i}) ∈ signatureLattice 1)
    (A : Finset β) :
    pullback F (booleanMonomial A) ∈ signatureLattice (A.card : ℤ) := by
  have h := product_mem_level A (fun i => pullback F (booleanMonomial {i}))
    (fun i _ => hF i)
  have heq : pullback F (booleanMonomial A) =
      ∏ i ∈ A, pullback F (booleanMonomial {i}) := by
    rw [monomial_eq_product]
    funext S
    simp [pullback, Finset.prod_apply]
  rwa [← heq] at h

/-- Any map whose coordinate functions are in Λ₁ preserves every Λ_s. -/
theorem pullback_preserves (F : Finset α → Finset β)
    (hF : ∀ i : β, pullback F (booleanMonomial {i}) ∈ signatureLattice 1)
    (s : ℤ) (f : Finset β → ℤ) (hf : f ∈ signatureLattice s) :
    pullback F f ∈ signatureLattice s := by
  obtain ⟨c, hc, rfl⟩ := hf
  rw [evaluate_eq_sum, map_sum]
  apply Submodule.sum_mem
  intro A _
  rw [map_smul]
  obtain ⟨k, hk⟩ := hc A
  rw [hk, mul_comm, mul_smul]
  apply Submodule.smul_mem
  exact power_smul_mem (A.card : ℤ) s (pullback F (booleanMonomial A))
    (pullback_monomial_mem F hF A)

/-- An arbitrary Boolean affine map: each output bit is a translated parity sum. -/
def booleanAffine (rows : β → Finset α) (bias : β → Bool) (S : Finset α) : Finset β :=
  Finset.univ.filter fun i => affineCoordinate (rows i) (bias i) S = 1

omit [Fintype α] [DecidableEq β] in
/-- This is precisely row-wise matrix multiplication and translation modulo two. -/
theorem booleanAffine_mem (rows : β → Finset α) (bias : β → Bool)
    (S : Finset α) (i : β) :
    i ∈ booleanAffine rows bias S ↔
      ((rows i ∩ S).card + if bias i then 1 else 0) % 2 = 1 := by
  simp only [booleanAffine, Finset.mem_filter, Finset.mem_univ, true_and]
  cases hb : bias i <;>
    simp only [affineCoordinate, hb, Bool.false_eq_true, ↓reduceIte,
      Pi.sub_apply, Pi.one_apply, parityCoordinate]
  · omega
  · omega

omit [Fintype α] in
theorem booleanAffine_coordinate (rows : β → Finset α) (bias : β → Bool) (i : β) :
    pullback (booleanAffine rows bias) (booleanMonomial {i}) =
      affineCoordinate (rows i) (bias i) := by
  funext S
  have h := affineCoordinate_bit (rows i) (bias i) S
  rcases h with h | h <;>
    simp [pullback, booleanMonomial, booleanAffine, h]

/-- Pullback by every Boolean affine map preserves the complete integral lattice. -/
theorem affine_pullback_preserves (rows : β → Finset α) (bias : β → Bool)
    (s : ℤ) (f : Finset β → ℤ) (hf : f ∈ signatureLattice s) :
    pullback (booleanAffine rows bias) f ∈ signatureLattice s := by
  apply pullback_preserves _ ?_ s f hf
  intro i
  rw [booleanAffine_coordinate]
  exact affineCoordinate_mem_one (rows i) (bias i)

/-- An affine inverse turns preservation into coordinate-invariance. -/
theorem affine_pullback_invariant
    (rows : β → Finset α) (bias : β → Bool)
    (inverseRows : α → Finset β) (inverseBias : α → Bool)
    (hinverse : Function.RightInverse (booleanAffine inverseRows inverseBias)
      (booleanAffine rows bias)) (s : ℤ) (f : Finset β → ℤ) :
    pullback (booleanAffine rows bias) f ∈ signatureLattice s ↔
      f ∈ signatureLattice s := by
  constructor
  · intro hf
    have h := affine_pullback_preserves inverseRows inverseBias s
      (pullback (booleanAffine rows bias) f) hf
    have heq : pullback (booleanAffine inverseRows inverseBias)
        (pullback (booleanAffine rows bias) f) = f := by
      funext S
      exact congrArg f (hinverse S)
    rwa [heq] at h
  · exact affine_pullback_preserves rows bias s f

/-- A permutation preserving the lattice in one direction preserves it in both.
Finite order supplies the inverse without any assumption on its coordinate formula. -/
theorem permutation_pullback_invariant (e : Equiv.Perm (Finset α))
    (hpres : ∀ f : Finset α → ℤ, ∀ s : ℤ,
      f ∈ signatureLattice s → pullback e f ∈ signatureLattice s)
    (s : ℤ) (f : Finset α → ℤ) :
    pullback e f ∈ signatureLattice s ↔ f ∈ signatureLattice s := by
  have hp : ∀ (n : ℕ) (g : Finset α → ℤ), g ∈ signatureLattice s →
      pullback (e ^ n) g ∈ signatureLattice s := by
    intro n
    induction n with
    | zero => intro g hg; simpa [pullback] using hg
    | succ n ih =>
        intro g hg
        have h := hpres _ s (ih g hg)
        simpa [pow_succ, pullback, Equiv.Perm.mul_apply] using h
  constructor
  · intro hf
    have h := hp (orderOf e - 1) (pullback e f) hf
    have hpow : e ^ ((orderOf e - 1) + 1) = 1 := by
      rw [Nat.sub_add_cancel (by have := orderOf_pos e; omega), pow_orderOf_eq_one]
    have heq : pullback (e ^ (orderOf e - 1)) (pullback e f) = f := by
      funext S
      change f ((e * e ^ (orderOf e - 1)) S) = f S
      rw [← pow_succ', hpow]
      rfl
    rwa [heq] at h
  · exact hpres f s

/-- Invariance under every invertible Boolean affine coordinate transformation.
Only bijectivity of the affine map is required; an affine inverse is not assumed. -/
theorem affine_bijective_invariant (rows : α → Finset α) (bias : α → Bool)
    (hbij : Function.Bijective (booleanAffine rows bias))
    (s : ℤ) (f : Finset α → ℤ) :
    pullback (booleanAffine rows bias) f ∈ signatureLattice s ↔
      f ∈ signatureLattice s := by
  let e : Equiv.Perm (Finset α) := Equiv.ofBijective (booleanAffine rows bias) hbij
  exact permutation_pullback_invariant e
    (fun g t hg => affine_pullback_preserves rows bias t g hg) s f

/-- Equality of actual submodules under any invertible affine relabeling. -/
theorem affine_submodule_invariance (rows : α → Finset α) (bias : α → Bool)
    (hbij : Function.Bijective (booleanAffine rows bias)) (s : ℤ) :
    (signatureLattice s).comap (pullback (booleanAffine rows bias)) =
      signatureLattice s := by
  ext f
  exact affine_bijective_invariant rows bias hbij s f

#print axioms monomial_union
#print axioms evaluate_eq_sum
#print axioms monomial_scalar_mem
#print axioms monomial_mem_level
#print axioms monomial_product_scalar
#print axioms union_exponent_le
#print axioms mul_mem
#print axioms shift_exponent_le
#print axioms power_smul_mem
#print axioms one_mem_zero
#print axioms coordinate_mem_one
#print axioms one_mem_one
#print axioms xor_mem_one
#print axioms parityCoordinate_bit
#print axioms parityCoordinate_insert
#print axioms parityCoordinate_mem_one
#print axioms affineCoordinate_bit
#print axioms affineCoordinate_mem_one
#print axioms monomial_eq_product
#print axioms product_mem_level
#print axioms pullback_monomial_mem
#print axioms pullback_preserves
#print axioms booleanAffine_mem
#print axioms booleanAffine_coordinate
#print axioms affine_pullback_preserves
#print axioms affine_pullback_invariant
#print axioms permutation_pullback_invariant
#print axioms affine_bijective_invariant
#print axioms affine_submodule_invariance

end Verification.AffineSignature

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.AffineSignature.affineCoordinate
#print axioms Verification.AffineSignature.booleanAffine
#print axioms Verification.AffineSignature.parityCoordinate
#print axioms Verification.AffineSignature.pullback
#print axioms Verification.AffineSignature.xorFunction
