/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FullMatrixSelectedSplit
import Verification.IndependentChartIndex
import Verification.FiniteDynkinClassificationInput
import Verification.FiniteMatrixRowSplitting

/-!
# Principal Coefficient Seed

The literal principal-coefficient seed has the identity frozen block.
Its full integer splitting and every required independent AS family are
proved, rather than assumed as an additional hypothesis of the main theorem.
-/
noncomputable section
namespace Verification.PrincipalCoefficientSeed
open Classical Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)

def matrix : Matrix (Fin n⊕Fin n) (Fin n⊕Empty) ℤ := fun r c=>match c with
  | .inl i=>match r with
    | .inl j=>B j i
    | .inr j=>if j=i then 1 else 0
  | .inr z=>z.elim

def projection : ((Fin n⊕Fin n)→ℤ)→ₗ[ℤ](Fin n→ℤ) where
  toFun x i:=x (Sum.inr i)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

theorem left : (projection (n:=n)).comp (Matrix.mulVecLin (fun r i=>matrix B r (Sum.inl i)))=LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext i
  change (∑j,(if i=j then (1:ℤ) else 0)*x j)=x i
  simp

theorem RFR : FiniteMatrixRowSplitting.RFR (fun r i=>matrix B r (Sum.inl i)) :=
  FiniteMatrixRowSplitting.rows_of_left _ (projection (n:=n)) (left B)

include B in
theorem support (h : FiniteDynkinClassificationInput.FiniteCartan B) (i j : Fin n) :
    earlierWeights (Fin n) n (matrix B) i j=0 ↔ laterWeights (Fin n) n (matrix B) i j=0 := by
  change (B i j).toNat=0 ↔ (-B j i).toNat=0
  rw [Int.toNat_eq_zero,Int.toNat_eq_zero]
  obtain ⟨d,hd,hS,_⟩:=h
  have hi:=hd i
  have hj:=hd j
  have hh:=hS i j
  constructor
  · intro h
    have h' : (B i j:ℝ)≤0 := by exact_mod_cast h
    have h'' : -(B j i:ℝ)≤0 := by nlinarith
    exact_mod_cast h''
  · intro h
    have h' : -(B j i:ℝ)≤0 := by exact_mod_cast h
    have h'' : (B i j:ℝ)≤0 := by nlinarith
    exact_mod_cast h''

theorem selected_AS
    (hpos : ∀ a i : Fin n, ¬ a < i → (B a i).toNat=0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B a i).toNat=0)
    (hfinite : FiniteDynkinClassificationInput.FiniteCartan B)
    (I : Finset (Fin n)) (hI : Independent (laterWeights (Fin n) n (matrix B)) I) :
    AnticliqueSubcolumns.AS (fun r i=>matrix B r (Sum.inl i)) I :=
  FullMatrixSelectedSplit.AS _ I (projection (n:=n)) (left B)
    (fun i hi j hj=>IndependentChartIndex.independent_principal_zero (Fin n) n I (matrix B)
      hpos hneg (support B hfinite) hI i j hi hj)

#print axioms matrix
#print axioms projection
#print axioms left
#print axioms RFR
#print axioms support
#print axioms selected_AS
end Verification.PrincipalCoefficientSeed
