/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualFreezingRows
import Verification.QuotientZeroProduct
import Verification.GlobalSelectedColumns

/-!
# Actual Residual Columns

The actual residual selected matrix is the unchanged remaining-row
block together with the original neighbour/frozen columns reduced modulo
the removed column. The manuscript's original AS condition implies its
injectivity and saturation after a proved lattice identification.
-/
noncomputable section
namespace Verification.ActualResidualColumns
open Verification.ActualFreezingRows Verification.FreezingSelectedColumns
open Verification.ActualFreezingDivisor Verification.FrozenAcyclicCover
open Verification.ActualFreezingCoefficient Verification.AnticliqueSubcolumns
open Verification.FreezingLattice Verification.ExchangeOpenCover
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
attribute [local instance] Verification.ActualFreezingConstraint.remainingFintype
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)
variable (I : Finset (Fin n))

def neighborColumn (w : Fin n) : (Neighbor κ n B v ⊕ κ) →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm
    (fun a => B (ActualDivisorPresentation.invertedOriginal κ n B v a) (Sum.inl w))

abbrev ResidualRows := (Outside κ n B v I →₀ ℤ) ×
  (((Neighbor κ n B v ⊕ κ) →₀ ℤ) ⧸ LinearMap.range (columnMap κ n B v))

def residualColumn (i : I) : ResidualRows κ n B v I :=
  (Finsupp.equivFunOnFinite.symm (fun a => B (Sum.inl a.val.val) (Sum.inl i.val)),
    (LinearMap.range (columnMap κ n B v)).mkQ (neighborColumn κ n B v i.val))

def residualMatrix : (I →₀ ℤ) →ₗ[ℤ] ResidualRows κ n B v I :=
  Finsupp.linearCombination ℤ (residualColumn κ n B v I)

variable (hv : v ∉ I)
variable (hn : ∀ i ∈ I, ¬ ExchangeRing.Adjacent (laterWeights κ n B) v i)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)

def rowQuotientEquiv :
    ((Rows (C := κ) (insert v I) →₀ ℤ) ⧸ firstSpan (selectedWithHead κ n B v I hv)) ≃ₗ[ℤ]
      ResidualRows κ n B v I :=
  QuotientZeroProduct.quotientEquiv (rowLinear κ n B v I hn)
    (selectedWithHead κ n B v I hv) (columnMap κ n B v)
      (rowLinear_head κ n B v I hn hpos hneg hsupport hv)

omit hn hpos hneg hsupport [Fintype κ] in
theorem coefficientEquiv_tail (i : I) : coefficientEquiv n v I hv (0,Finsupp.single i 1) =
    Finsupp.single (⟨i.val,Finset.mem_insert_of_mem i.property⟩ : (insert v I : Finset (Fin n))) 1 := by
  classical
  have hi : i.val ≠ v := by intro h; exact hv (h ▸ i.property)
  ext j
  by_cases hj : j.val = v
  · simp [coefficientEquiv, Finsupp.single_apply, Subtype.ext_iff, hj, hi, Ne.symm hi]
  · simp [coefficientEquiv, Finsupp.single_apply, Subtype.ext_iff, hj]

theorem columns_agree :
    (rowQuotientEquiv κ n B v I hv hn hpos hneg hsupport).toLinearMap.comp
      (residualSelectedMap κ n B v I hv) = residualMatrix κ n B v I := by
  classical
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, residualMatrix,
    Finsupp.linearCombination_single, one_smul]
  change QuotientZeroProduct.quotientEquiv _ _ _ _
    ((firstSpan _).mkQ (selectedWithHead κ n B v I hv (0,Finsupp.single i 1))) = _
  rw [QuotientZeroProduct.quotientEquiv_mk]
  have hi : selectedWithHead κ n B v I hv (0,Finsupp.single i 1) =
      column (fun a w => B a (Sum.inl w)) (insert v I) ⟨i.val,Finset.mem_insert_of_mem i.property⟩ := by
    change selectedMap _ _ (coefficientEquiv n v I hv (0,Finsupp.single i 1)) = _
    rw [coefficientEquiv_tail]
    simp only [selectedMap, Finsupp.linearCombination_single, one_smul]
  rw [hi]
  apply Prod.ext
  · ext a
    rw [rowLinear_left]
    rfl
  · apply congrArg (LinearMap.range (columnMap κ n B v)).mkQ
    ext a
    rw [rowLinear_right]
    cases a <;> rfl

include hv hn hpos hneg hsupport
theorem residual_AS (hAS : AS (fun a w => B a (Sum.inl w)) (insert v I)) :
    Function.Injective (residualMatrix κ n B v I) ∧
      Saturated (LinearMap.range (residualMatrix κ n B v I)) := by
  have h := FreezingSelectedColumns.residual_AS κ n B v I hv hAS
  rw [← columns_agree κ n B v I hv hn hpos hneg hsupport]
  exact ⟨(rowQuotientEquiv κ n B v I hv hn hpos hneg hsupport).injective.comp h.1,
    (GlobalSelectedColumns.saturated_equiv _ _).mpr h.2⟩

theorem residual_AS_of_allAS
    (hall : ∀ J : Finset (Fin n), Independent (laterWeights κ n B) J →
      AS (fun a w => B a (Sum.inl w)) J)
    (hI : Independent (laterWeights κ n B) I) :
    Function.Injective (residualMatrix κ n B v I) ∧
      Saturated (LinearMap.range (residualMatrix κ n B v I)) :=
  residual_AS κ n B v I hv hn hpos hneg hsupport
    (hall _ (insert_independent κ n B v I hI hn))

#print axioms neighborColumn
#print axioms ResidualRows
#print axioms residualColumn
#print axioms residualMatrix
#print axioms rowQuotientEquiv
#print axioms coefficientEquiv_tail
#print axioms columns_agree
#print axioms residual_AS
#print axioms residual_AS_of_allAS
end Verification.ActualResidualColumns
