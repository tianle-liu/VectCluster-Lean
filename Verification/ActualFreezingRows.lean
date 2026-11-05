/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingSelectedColumns
import Verification.ActualFreezingColumnAS
import Mathlib.LinearAlgebra.Finsupp.SumProd

/-!
# Actual Freezing Rows

The actual deleted rows for {v} union I split into the remaining
mutable rows outside I and all neighbour/frozen rows. This is the row
identification required to match the residual AS quotient with the
residual exchange presentation.
-/
noncomputable section
namespace Verification.ActualFreezingRows
open Verification.AnticliqueSubcolumns Verification.FreezingIndex
open Verification.ActualFreezingDivisor Verification.FrozenAcyclicCover
open Verification.ActualFreezingCoefficient Verification.FreezingSelectedColumns
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
attribute [local instance] Verification.ActualFreezingConstraint.remainingFintype
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)
variable (I : Finset (Fin n))
variable (hn : ∀ i ∈ I, ¬ ExchangeRing.Adjacent (laterWeights κ n B) v i)

abbrev Outside := {i : Remaining κ n B v // i.val ∉ I}

def rowEquiv : Rows (C := κ) (insert v I) ≃ (Outside κ n B v I ⊕ (Neighbor κ n B v ⊕ κ)) := by
  classical
  refine {
    toFun := fun a => match a with
      | ⟨Sum.inl i,hi⟩ => if h : ExchangeRing.Adjacent (laterWeights κ n B) v i then Sum.inr (Sum.inl ⟨i,h⟩)
        else Sum.inl ⟨⟨i,⟨by intro he; subst i; exact hi v (Finset.mem_insert_self v I) rfl,h⟩⟩,
          by intro hm; exact hi i (Finset.mem_insert_of_mem hm) rfl⟩
      | ⟨Sum.inr c,_⟩ => Sum.inr (Sum.inr c)
    invFun := fun a => match a with
      | Sum.inl i => ⟨Sum.inl i.val.val,by
          intro w hw he
          have hh := Sum.inl.inj he
          subst w
          rcases Finset.mem_insert.mp hw with h | h
          · exact i.val.property.1 h
          · exact i.property h⟩
      | Sum.inr (Sum.inl a) => ⟨Sum.inl a.val,by
          intro w hw he
          have hh := Sum.inl.inj he
          subst w
          rcases Finset.mem_insert.mp hw with h | h
          · have hz : ¬ ExchangeRing.Adjacent (laterWeights κ n B) v v := by simp [ExchangeRing.Adjacent]
            have hadj := a.property
            rw [h] at hadj
            exact hz hadj
          · exact hn a.val h a.property⟩
      | Sum.inr (Sum.inr c) => ⟨Sum.inr c,by simp⟩
    left_inv := ?_
    right_inv := ?_ }
  · rintro ⟨a,ha⟩
    cases a with
    | inl i => dsimp only; split_ifs <;> rfl
    | inr c => rfl
  · intro a
    rcases a with i | (a | c)
    · simp only [dif_neg i.val.property.2]
    · rcases a with ⟨a,ha⟩
      simp only [dif_pos ha]
    · rfl

def rowLinear : (Rows (C := κ) (insert v I) →₀ ℤ) ≃ₗ[ℤ]
    (Outside κ n B v I →₀ ℤ) × ((Neighbor κ n B v ⊕ κ) →₀ ℤ) :=
  (Finsupp.domLCongr (rowEquiv κ n B v I hn)).trans (Finsupp.sumFinsuppLEquivProdFinsupp ℤ)

omit [Fintype κ] in
theorem rowLinear_left (z : Rows (C := κ) (insert v I) →₀ ℤ) (i : Outside κ n B v I) :
    (rowLinear κ n B v I hn z).1 i = z ((rowEquiv κ n B v I hn).symm (Sum.inl i)) := rfl

omit [Fintype κ] in
theorem rowLinear_right (z : Rows (C := κ) (insert v I) →₀ ℤ) (a : Neighbor κ n B v ⊕ κ) :
    (rowLinear κ n B v I hn z).2 a = z ((rowEquiv κ n B v I hn).symm (Sum.inr a)) := rfl

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
include hpos hneg hsupport

theorem rowLinear_head (hv : v ∉ I) (a : ℤ) :
    rowLinear κ n B v I hn (selectedWithHead κ n B v I hv (a,0)) =
      (0,columnMap κ n B v a) := by
  rw [selectedWithHead_head, map_smul]
  apply Prod.ext
  · ext i
    change a • (rowLinear κ n B v I hn (column _ _ _)).1 i = 0
    rw [rowLinear_left]
    change a * B (Sum.inl i.val.val) (Sum.inl v) = 0
    rw [FreezingSupport.remaining_column κ n B hpos hneg hsupport v i.val, mul_zero]
  · ext j
    change a • (rowLinear κ n B v I hn (column _ _ _)).2 j =
      (columnMap κ n B v a) j
    rw [rowLinear_right]
    change a * B ((rowEquiv κ n B v I hn).symm (Sum.inr j)).val (Sum.inl v) =
      a * distinguishedColumn κ n B v j
    rw [ActualFreezingColumnAS.distinguishedColumn_apply]
    cases j <;> rfl

#print axioms Outside
#print axioms rowEquiv
#print axioms rowLinear
#print axioms rowLinear_left
#print axioms rowLinear_right
#print axioms rowLinear_head
end Verification.ActualFreezingRows
