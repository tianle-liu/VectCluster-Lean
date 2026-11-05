/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RealClusterFiltration
import Verification.ExchangeOpenCover
import Verification.ActualSignLabels

/-!
# Real Acyclic Filtration

The acyclic support condition on the literal real exchange solution
space forces independent zero sets and bounds the actual open filtration.
-/
noncomputable section
namespace Verification.RealAcyclicFiltration
open Verification.RealClusterFiltration Verification.ExchangeGeometry
open Verification.ExchangeOpenCover Verification.AnticliqueSubcolumns
open scoped BigOperators
variable {C : Type} [Fintype C] {n : ℕ}
variable (B : (Fin n ⊕ C) → Fin n → ℤ)

def earlierWeights (a i : Fin n) : ℕ := (B (Sum.inl a) i).toNat
def laterWeights (i a : Fin n) : ℕ := (-B (Sum.inl a) i).toNat
def earlierCoefficient (p : Point B) (i : Fin n) : ℝ :=
  ∏ c, p.val.1 (Sum.inr c) ^ (B (Sum.inr c) i).toNat
def laterCoefficient (p : Point B) (i : Fin n) : ℝ :=
  ∏ c, p.val.1 (Sum.inr c) ^ (-B (Sum.inr c) i).toNat

theorem earlierCoefficient_ne_zero (p : Point B) (i : Fin n) :
    earlierCoefficient B p i≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro c _
  exact pow_ne_zero _ (p.property.1 c)

theorem ordered_equations
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) i).toNat=0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) i).toNat=0)
    (p : Point B) : ExchangeEquations (earlierWeights B) (laterWeights B)
      (fun i => p.val.1 (Sum.inl i)) p.val.2
      (earlierCoefficient B p) (laterCoefficient B p) := by
  intro i
  rw [p.property.2 i]
  unfold Verification.RealExchangeCharacters.exchange
  rw [Fintype.prod_sum_type,Fintype.prod_sum_type]
  unfold earlierCoefficient laterCoefficient earlierMonomial laterMonomial
  congr 1 <;> rw [mul_comm] <;> congr 1
  · apply Finset.prod_congr rfl
    intro a _
    by_cases ha : a < i
    · simp only [ha,if_true,earlierWeights]
    · simp only [ha,if_false,hpos a i ha]
  · apply Finset.prod_congr rfl
    intro a _
    by_cases ha : i < a
    · simp only [ha,if_true,laterWeights]
    · simp only [ha,if_false,hneg a i ha]

theorem actual_zeroSet_independent
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) i).toNat=0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) i).toNat=0)
    (hsupport : ∀ i j, earlierWeights B i j=0 ↔ laterWeights B i j=0)
    (p : Point B) : Independent (laterWeights B) (zeroSet B p) := by
  intro i hi j hj he
  have h := zero_set_independent (earlierWeights B) (laterWeights B)
    (fun i => p.val.1 (Sum.inl i)) p.val.2 (earlierCoefficient B p)
    (laterCoefficient B p) hsupport (earlierCoefficient_ne_zero B p)
    (ordered_equations B hpos hneg p) i j
    ((mem_zeroSet B p i).mp hi) ((mem_zeroSet B p j).mp hj)
  rcases he with ⟨hij,hv⟩ | ⟨hji,hv⟩
  · exact hv (h.1 hij)
  · exact hv (h.2 hji)

omit [Fintype C] in
theorem independent_zero_block
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) i).toNat=0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) i).toNat=0)
    (hsupport : ∀ i j, earlierWeights B i j=0 ↔ laterWeights B i j=0)
    (I : Finset (Fin n)) (hI : Independent (laterWeights B) I)
    (i j : I) : B (Sum.inl i.val) j.val=0 := by
  have hp : (B (Sum.inl i.val) j.val).toNat=0 := by
    by_cases hij : i.val < j.val
    · apply (hsupport i.val j.val).mpr
      by_contra hn
      exact hI i.val i.property j.val j.property (Or.inl ⟨hij,hn⟩)
    · exact hpos i.val j.val hij
  have hn : (-B (Sum.inl i.val) j.val).toNat=0 := by
    by_cases hji : j.val < i.val
    · by_contra hn
      exact hI j.val j.property i.val i.property (Or.inl ⟨hji,hn⟩)
    · exact hneg i.val j.val hji
  omega

theorem actual_zeroSet_bound
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) i).toNat=0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) i).toNat=0)
    (hsupport : ∀ i j, earlierWeights B i j=0 ↔ laterWeights B i j=0)
    (hAS : ∀ I, Independent (laterWeights B) I → AS B I) (p : Point B) :
    2*(zeroSet B p).card≤n+Fintype.card C := by
  simpa only [Fintype.card_fin] using ActualSignLabels.twice_card_le_dimension B
    (zeroSet B p) (hAS _ (actual_zeroSet_independent B hpos hneg hsupport p))

theorem omega_half_dimension
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) i).toNat=0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) i).toNat=0)
    (hsupport : ∀ i j, earlierWeights B i j=0 ↔ laterWeights B i j=0)
    (hAS : ∀ I, Independent (laterWeights B) I → AS B I) :
    omega B ((n+Fintype.card C)/2)=Set.univ := by
  ext p
  simp only [omega,Set.mem_setOf_eq,Set.mem_univ,iff_true]
  have := actual_zeroSet_bound B hpos hneg hsupport hAS p
  omega

#print axioms earlierWeights
#print axioms laterWeights
#print axioms earlierCoefficient
#print axioms laterCoefficient
#print axioms earlierCoefficient_ne_zero
#print axioms ordered_equations
#print axioms actual_zeroSet_independent
#print axioms independent_zero_block
#print axioms actual_zeroSet_bound
#print axioms omega_half_dimension
end Verification.RealAcyclicFiltration
