/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineSignature
import Mathlib.Data.Finset.Option

/-!
# Signature Residue

The integral lattice preservation in manuscript.tex:3054–3082, proved
on actual integer-valued Boolean functions. `none` is the framed normal
coordinate; the residue is positive minus negative. Affine changes and
restrictions are handled by the previously proved affine pullback theorem.
-/
namespace Verification.SignatureResidue
open Finset Verification.SignatureLattice Verification.AffineSignature
variable {α β : Type*} [Fintype α] [DecidableEq α]

/-- The literal signed difference in the real cellular differential. -/
def residue : (Finset (Option α) → ℤ) →ₗ[ℤ] (Finset α → ℤ) where
  toFun f S := f (S.image some) - f (insert none (S.image some))
  map_add' f g := by ext S; simp; ring
  map_smul' a f := by ext S; simp [mul_sub]

omit [Fintype α] in
theorem subset_positive (A : Finset (Option α)) (S : Finset α) :
    A ⊆ S.image some ↔ none ∉ A ∧ A.eraseNone ⊆ S := by
  constructor
  · intro h
    constructor
    · intro hn; simpa using h hn
    · intro a ha
      have := h (Finset.mem_eraseNone.mp ha)
      simpa using this
  · rintro ⟨hn, h⟩ a ha
    cases a with
    | none => exact (hn ha).elim
    | some a => simpa using h (Finset.mem_eraseNone.mpr ha)

omit [Fintype α] in
theorem subset_negative (A : Finset (Option α)) (S : Finset α) :
    A ⊆ insert none (S.image some) ↔ A.eraseNone ⊆ S := by
  constructor
  · intro h a ha
    have := h (Finset.mem_eraseNone.mp ha)
    simpa using this
  · intro h a ha
    cases a with
    | none => exact Finset.mem_insert_self _ _
    | some a => simpa using h (Finset.mem_eraseNone.mpr ha)

omit [Fintype α] in
theorem residue_monomial (A : Finset (Option α)) :
    residue (booleanMonomial A) =
      if none ∈ A then -booleanMonomial A.eraseNone else 0 := by
  funext S
  change (if A ⊆ S.image some then (1 : ℤ) else 0) -
      (if A ⊆ insert none (S.image some) then 1 else 0) = _
  simp only [subset_positive, subset_negative]
  by_cases hn : none ∈ A <;> simp [hn, booleanMonomial]

omit [Fintype α] in
theorem eraseNone_card (A : Finset (Option α)) (hn : none ∈ A) :
    A.eraseNone.card + 1 = A.card := by
  have hc := congrArg Finset.card (Finset.map_some_eraseNone A)
  rw [Finset.card_map, Finset.card_erase_of_mem hn] at hc
  have hpos := Finset.card_pos.mpr ⟨none, hn⟩
  omega

omit [Fintype α] in
theorem residue_exponent (A : Finset (Option α)) (hn : none ∈ A) (s : ℤ) :
    exponent (s-1) A.eraseNone = exponent s A := by
  have := eraseNone_card A hn
  unfold exponent
  congr 1
  omega

/-- Every level, including negative levels, goes to the next contracted level. -/
theorem residue_preserves_lattice (s : ℤ) (f : Finset (Option α) → ℤ)
    (hf : f ∈ signatureLattice s) : residue f ∈ signatureLattice (s-1) := by
  obtain ⟨c, hc, rfl⟩ := hf
  rw [evaluate_eq_sum, map_sum]
  apply Submodule.sum_mem
  intro A _
  rw [map_smul, residue_monomial]
  by_cases hn : none ∈ A
  · rw [if_pos hn, smul_neg]
    apply Submodule.neg_mem
    apply monomial_scalar_mem
    rw [residue_exponent A hn s]
    exact hc A
  · simp only [if_neg hn, smul_zero]
    exact Submodule.zero_mem _

variable [Fintype β] [DecidableEq β]
/-- A face expressed in arbitrary affine Boolean coordinates still preserves
its integral lattices with exactly the required one-step level shift. -/
theorem affine_residue_preserves (rows : β → Finset (Option α)) (bias : β → Bool)
    (s : ℤ) (f : Finset β → ℤ) (hf : f ∈ signatureLattice s) :
    residue (pullback (booleanAffine rows bias) f) ∈ signatureLattice (s-1) :=
  residue_preserves_lattice s _ (affine_pullback_preserves rows bias s f hf)

#print axioms residue
#print axioms subset_positive
#print axioms subset_negative
#print axioms residue_monomial
#print axioms eraseNone_card
#print axioms residue_exponent
#print axioms residue_preserves_lattice
#print axioms affine_residue_preserves
end Verification.SignatureResidue
