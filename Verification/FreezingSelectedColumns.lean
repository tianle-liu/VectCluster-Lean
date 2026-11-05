/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingQuotientAS
import Verification.AnticliqueSubcolumns
import Verification.FrozenAcyclicCover

/-!
# Freezing Selected Columns

The AS quotient step for actual deleted-row exchange columns. For
the original selected set {v} union I, split the actual coefficient of v,
then quotient its actual column. No AS condition on the residual map is
assumed.
-/
noncomputable section
namespace Verification.FreezingSelectedColumns
open Verification.AnticliqueSubcolumns Verification.FreezingLattice
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)
variable (I : Finset (Fin n)) (hv : v ∉ I)

def coefficientEquiv : (ℤ × (I →₀ ℤ)) ≃ₗ[ℤ] ((insert v I : Finset (Fin n)) →₀ ℤ) := by
  classical
  let forward (p : ℤ × (I →₀ ℤ)) : ((insert v I : Finset (Fin n)) →₀ ℤ) :=
    Finsupp.equivFunOnFinite.symm (fun j => if h : j.val = v then p.1
      else p.2 ⟨j.val, (Finset.mem_insert.mp j.property).resolve_left h⟩)
  let backward (z : ((insert v I : Finset (Fin n)) →₀ ℤ)) : ℤ × (I →₀ ℤ) :=
    (z ⟨v,Finset.mem_insert_self v I⟩,
      Finsupp.equivFunOnFinite.symm (fun i => z ⟨i.val,Finset.mem_insert_of_mem i.property⟩))
  exact {
    toFun := forward
    invFun := backward
    left_inv := by
      rintro ⟨a,u⟩
      apply Prod.ext
      · simp [forward, backward]
      · ext i
        have hi : i.val ≠ v := by intro h; exact hv (h ▸ i.property)
        simp [forward, backward, hi]
    right_inv := by
      intro z
      ext j
      by_cases hj : j.val = v
      · have he : j = ⟨v,Finset.mem_insert_self v I⟩ := Subtype.ext hj
        subst j
        simp [forward, backward]
      · simp [forward, backward, hj]
    map_add' := by
      intro p q
      ext j
      by_cases hj : j.val = v <;> simp [forward, hj]
    map_smul' := by
      intro a p
      ext j
      by_cases hj : j.val = v <;> simp [forward, hj] }

def selectedWithHead : (ℤ × (I →₀ ℤ)) →ₗ[ℤ] (Rows (C := κ) (insert v I) →₀ ℤ) :=
  (selectedMap (fun a w => B a (Sum.inl w)) (insert v I)).comp
    (coefficientEquiv n v I hv).toLinearMap

omit [Fintype κ] in
theorem coefficientEquiv_head (a : ℤ) : coefficientEquiv n v I hv (a,0) =
    Finsupp.single (⟨v,Finset.mem_insert_self v I⟩ : (insert v I : Finset (Fin n))) a := by
  classical
  ext j
  simp [coefficientEquiv, Finsupp.single_apply, Subtype.ext_iff, eq_comm]

theorem selectedWithHead_head (a : ℤ) : selectedWithHead κ n B v I hv (a,0) =
    a • column (fun x w => B x (Sum.inl w)) (insert v I) ⟨v,Finset.mem_insert_self v I⟩ := by
  change selectedMap _ _ (coefficientEquiv n v I hv (a,0)) = _
  rw [coefficientEquiv_head]
  exact Finsupp.linearCombination_single _ _ _

theorem selectedWithHead_range : LinearMap.range (selectedWithHead κ n B v I hv) =
    LinearMap.range (selectedMap (fun a w => B a (Sum.inl w)) (insert v I)) := by
  apply le_antisymm
  · rintro _ ⟨p,rfl⟩
    exact ⟨coefficientEquiv n v I hv p,rfl⟩
  · rintro _ ⟨p,rfl⟩
    refine ⟨(coefficientEquiv n v I hv).symm p,?_⟩
    change selectedMap _ _ (coefficientEquiv n v I hv ((coefficientEquiv n v I hv).symm p)) = _
    rw [LinearEquiv.apply_symm_apply]

def residualSelectedMap : (I →₀ ℤ) →ₗ[ℤ]
    ((Rows (C := κ) (insert v I) →₀ ℤ) ⧸ firstSpan (selectedWithHead κ n B v I hv)) :=
  residualColumns (selectedWithHead κ n B v I hv)

theorem residual_AS (hAS : AS (fun a w => B a (Sum.inl w)) (insert v I)) :
    Function.Injective (residualSelectedMap κ n B v I hv) ∧
      Saturated (LinearMap.range (residualSelectedMap κ n B v I hv)) := by
  have hi : Function.Injective (selectedWithHead κ n B v I hv) :=
    hAS.1.comp (coefficientEquiv n v I hv).injective
  have hs : Saturated (LinearMap.range (selectedWithHead κ n B v I hv)) := by
    rw [selectedWithHead_range]
    exact hAS.2
  exact ⟨FreezingQuotientAS.residual_injective _ hi,
    FreezingQuotientAS.residual_saturated _ hs⟩

omit hv [Fintype κ] in
theorem insert_independent (hI : Independent (laterWeights κ n B) I)
    (hn : ∀ i ∈ I, ¬ ExchangeRing.Adjacent (laterWeights κ n B) v i) :
    Independent (laterWeights κ n B) (insert v I) := by
  classical
  intro a ha b hb
  by_cases hav : a = v
  · subst a
    by_cases hbv : b = v
    · subst b
      simp [ExchangeRing.Adjacent]
    · exact hn b ((Finset.mem_insert.mp hb).resolve_left hbv)
  · have haI := (Finset.mem_insert.mp ha).resolve_left hav
    by_cases hbv : b = v
    · subst b
      intro h
      exact hn a haI (h.elim Or.inr Or.inl)
    · exact hI a haI b ((Finset.mem_insert.mp hb).resolve_left hbv)

theorem residual_AS_of_allAS
    (hall : ∀ J : Finset (Fin n), Independent (laterWeights κ n B) J →
      AS (fun a w => B a (Sum.inl w)) J)
    (hI : Independent (laterWeights κ n B) I)
    (hn : ∀ i ∈ I, ¬ ExchangeRing.Adjacent (laterWeights κ n B) v i) :
    Function.Injective (residualSelectedMap κ n B v I hv) ∧
      Saturated (LinearMap.range (residualSelectedMap κ n B v I hv)) :=
  residual_AS κ n B v I hv (hall _ (insert_independent κ n B v I hI hn))

#print axioms coefficientEquiv
#print axioms selectedWithHead
#print axioms coefficientEquiv_head
#print axioms selectedWithHead_head
#print axioms selectedWithHead_range
#print axioms residualSelectedMap
#print axioms residual_AS
#print axioms insert_independent
#print axioms residual_AS_of_allAS
end Verification.FreezingSelectedColumns
