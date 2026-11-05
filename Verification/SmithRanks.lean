/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmithCharacters
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.Sum

/-!
# Smith Ranks

Ranks of the constrained and unconstrained Smith coordinates.
These identities supply the exponent d-2|I| from the original column map.
-/
namespace Verification.SmithRanks
open Verification.SmithCharacters
variable {M P ι κ : Type*} [AddCommGroup M] [AddCommGroup P]

theorem smith_source_rank [Fintype κ]
    (f : P →ₗ[ℤ] M) (hf : Function.Injective f) (b : Basis κ ℤ P)
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n) :
    n = Fintype.card κ := by
  have h1 := Module.finrank_eq_card_basis (smithSourceBasis f hf s)
  have h2 := Module.finrank_eq_card_basis b
  simpa only [Fintype.card_fin] using h1.symm.trans h2

noncomputable def coordinateSplit {n : ℕ} (j : Fin n ↪ ι) :
    (Fin n ⊕ {i : ι // i ∉ Set.range j}) ≃ ι := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective j j.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun i => i ∈ Set.range j))

theorem coordinateSplit_inl {n : ℕ} (j : Fin n ↪ ι) (i : Fin n) :
    coordinateSplit j (Sum.inl i) = j i := rfl

theorem coordinateSplit_inr {n : ℕ} (j : Fin n ↪ ι) (i : {i : ι // i ∉ Set.range j}) :
    coordinateSplit j (Sum.inr i) = i := rfl

theorem complement_rank [Fintype ι] {n : ℕ} (j : Fin n ↪ ι) :
    Nat.card {i : ι // i ∉ Set.range j} + n = Fintype.card ι := by
  classical
  have h := Fintype.card_congr (coordinateSplit j)
  rw [Fintype.card_sum, Fintype.card_fin, ← Nat.card_eq_fintype_card] at h
  omega

theorem smith_free_rank [Fintype ι] [Fintype κ]
    (f : P →ₗ[ℤ] M) (hf : Function.Injective f) (b : Basis κ ℤ P)
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n) :
    Nat.card {i : ι // i ∉ Set.range s.f} + Fintype.card κ = Fintype.card ι := by
  rw [← smith_source_rank f hf b s]
  exact complement_rank s.f

#print axioms smith_source_rank
#print axioms coordinateSplit
#print axioms coordinateSplit_inl
#print axioms coordinateSplit_inr
#print axioms complement_rank
#print axioms smith_free_rank
end Verification.SmithRanks
