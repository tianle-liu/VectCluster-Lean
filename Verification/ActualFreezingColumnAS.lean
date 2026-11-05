/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualFreezingCoefficient
import Verification.AnticliqueSubcolumns

/-!
# Actual Freezing Column AS

The actual neighbour/frozen column used in the freezing torus fiber
inherits AS from the manuscript's selected singleton column. The rows
removed here are proved zero from the original support conditions.
-/
noncomputable section
namespace Verification.ActualFreezingColumnAS
open Verification.ActualFreezingCoefficient Verification.ActualFreezingConstraint
open Verification.ActualFreezingDivisor Verification.FrozenAcyclicCover
open Verification.AnticliqueSubcolumns
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)

def singletonVertex : ({v} : Finset (Fin n)) := ⟨v,by simp⟩

def rowEmbedding : ((Neighbor κ n B v ⊕ κ) →₀ ℤ) →ₗ[ℤ]
    (Rows (C := κ) ({v} : Finset (Fin n)) →₀ ℤ) := by
  classical
  let g (m : (Neighbor κ n B v ⊕ κ) →₀ ℤ) (a : Rows (C := κ) ({v} : Finset (Fin n))) :=
    match a.val with
    | Sum.inl i => if h : ExchangeRing.Adjacent (laterWeights κ n B) v i then m (Sum.inl ⟨i,h⟩) else 0
    | Sum.inr c => m (Sum.inr c)
  exact {
    toFun := fun m => Finsupp.equivFunOnFinite.symm (g m)
    map_add' := by
      intro m p
      ext ⟨a,ha⟩
      cases a with
      | inl i => by_cases h : ExchangeRing.Adjacent (laterWeights κ n B) v i <;> simp [g,h]
      | inr c => rfl
    map_smul' := by
      intro z m
      ext ⟨a,ha⟩
      cases a with
      | inl i => by_cases h : ExchangeRing.Adjacent (laterWeights κ n B) v i <;> simp [g,h]
      | inr c => rfl }

theorem distinguishedColumn_apply (a : Neighbor κ n B v ⊕ κ) :
    distinguishedColumn κ n B v a = columnEntry κ n B v a := by
  classical
  cases a <;> simp [distinguishedColumn, ExchangeCharacters.column, Finsupp.sum_apply,
    Finsupp.single_apply, Finsupp.smul_apply]

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
include hpos hneg hsupport

theorem embedded_column : rowEmbedding κ n B v (distinguishedColumn κ n B v) =
    column (fun a w => B a (Sum.inl w)) ({v} : Finset (Fin n)) (singletonVertex n v) := by
  classical
  ext ⟨a,ha⟩
  cases a with
  | inl i =>
    change (if h : ExchangeRing.Adjacent (laterWeights κ n B) v i then
      distinguishedColumn κ n B v (Sum.inl ⟨i,h⟩) else 0) = B (Sum.inl i) (Sum.inl v)
    by_cases h : ExchangeRing.Adjacent (laterWeights κ n B) v i
    · rw [dif_pos h, distinguishedColumn_apply]
      rfl
    · rw [dif_neg h]
      exact (FreezingSupport.nonadjacent_entry_transpose κ n B hpos hneg hsupport v i h).symm
  | inr c =>
    change distinguishedColumn κ n B v (Sum.inr c) = _
    rw [distinguishedColumn_apply]
    rfl

theorem maps_compatible : (rowEmbedding κ n B v).comp (columnMap κ n B v) =
    (selectedMap (fun a w => B a (Sum.inl w)) ({v} : Finset (Fin n))).comp
      (Finsupp.lsingle (singletonVertex n v)) := by
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, columnMap, LinearMap.toSpanSingleton_apply, one_smul,
    Finsupp.lsingle_apply, selectedMap, Finsupp.linearCombination_single]
  exact embedded_column κ n B v hpos hneg hsupport

theorem singleton_AS
    (hAS : AS (fun a w => B a (Sum.inl w)) ({v} : Finset (Fin n))) :
    Function.Injective (columnMap κ n B v) ∧
      Verification.FreezingLattice.Saturated (LinearMap.range (columnMap κ n B v)) := by
  obtain ⟨e,he⟩ := PrimitiveLattice.primitive_columns_split_compatible
    (selectedMap (fun a w => B a (Sum.inl w)) ({v} : Finset (Fin n))) hAS.1 hAS.2
  let r := (Finsupp.lapply (singletonVertex n v)).comp
    ((LinearMap.fst ℤ _ _).comp (e.toLinearMap.comp (rowEmbedding κ n B v)))
  have hleft : Function.LeftInverse r (columnMap κ n B v) := by
    intro z
    change (e (rowEmbedding κ n B v (columnMap κ n B v z))).1 (singletonVertex n v) = z
    have h := LinearMap.congr_fun (maps_compatible κ n B v hpos hneg hsupport) z
    change rowEmbedding κ n B v (columnMap κ n B v z) =
      selectedMap (fun a w => B a (Sum.inl w)) ({v} : Finset (Fin n))
        (Finsupp.single (singletonVertex n v) z) at h
    rw [h,he]
    exact Finsupp.single_eq_same
  exact ⟨hleft.injective,CliqueSaturation.split_range_saturated _ _ hleft⟩

#print axioms singletonVertex
#print axioms rowEmbedding
#print axioms distinguishedColumn_apply
#print axioms embedded_column
#print axioms maps_compatible
#print axioms singleton_AS
end Verification.ActualFreezingColumnAS
