/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegerReductionEquiv
import Verification.OriginalWittRelationRank
import Verification.ExplicitStratumTorus
import Verification.GlobalSelectedColumns

/-!
# Original Witt Character Splitting

The binary splitting used for the Witt quotient is obtained from the
same integral splitting that parametrizes the actual AS character fiber.
The normal coordinates and original selected columns are preserved.
-/
noncomputable section
open scoped Classical
namespace Verification.OriginalWittCharacterSplitting
open Verification.IndependentChartIndex Verification.OriginalWittQuotient
open Verification.OriginalWittRelationRank
variable (κ : Type) [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def splitBits : Bits (Fin n) κ ≃ₗ[ZMod 2]
    ((I → ZMod 2) × ((Other n I ⊕ κ) → ZMod 2)) :=
  (LinearEquiv.piCongrLeft' (ZMod 2) (fun _ : Fin n ⊕ κ => ZMod 2)
    (originals κ n I)).trans
    (LinearEquiv.sumArrowLequivProdArrow (Selected n I) (Other n I ⊕ κ) (ZMod 2) (ZMod 2))

omit [Fintype κ] in
theorem splitBits_apply (x : Bits (Fin n) κ) : splitBits κ n I x =
    ((fun i => x (Sum.inl i.val)),fun a => x ((originals κ n I).symm (Sum.inr a))) := rfl

theorem splitBits_relation
    (hz : ∀ i j : I, B (Sum.inl j.val) (Sum.inl i.val)=0) (x : (I ⊕ I) → ZMod 2) :
    splitBits κ n I (relationMap (fun a v => B a (Sum.inl v)) I x) =
      (x ∘ Sum.inl,IntegerLinearReduction.reduce (GlobalExchangeSmooth.selectedMap κ n B I)
        (x ∘ Sum.inr)) := by
  rw [splitBits_apply]
  apply Prod.ext
  · funext j
    exact normal_coordinate _ I hz x j
  · funext a
    change relationMap (fun a v => B a (Sum.inl v)) I x
      ((originals κ n I).symm (Sum.inr a)) =
        IntegerLinearReduction.reduce (GlobalExchangeSmooth.selectedMap κ n B I) (x ∘ Sum.inr) a
    rw [relationMap_apply,IntegerLinearReduction.reduce_apply]
    have hn (i : I) : (originals κ n I).symm (Sum.inr a) ≠ Sum.inl i.val := by
      intro he
      have h := congrArg (originals κ n I) he
      rw [Equiv.apply_symm_apply] at h
      have hi : originals κ n I (Sum.inl i.val) = Sum.inl i :=
        (originals κ n I).apply_symm_apply (Sum.inl i)
      rw [hi] at h
      cases h
    simp only [Pi.single_apply,hn,if_false,zero_mul,Finset.sum_const_zero,zero_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [GlobalExchangeSmooth.selectedMap,ActualOpenGeometry.columnMap_single,
      ActualColumnRank.actual_column_apply]
    rfl

variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

def splitting : Bits (Fin n) κ ≃ₗ[ZMod 2]
    (((I ⊕ I) → ZMod 2) × (Fin (ExplicitStratumTorus.torusRank κ n I B) → ZMod 2)) :=
  ((splitBits κ n I).trans
    ((LinearEquiv.refl (ZMod 2) (I → ZMod 2)).prodCongr
      (IntegerReductionEquiv.productEquiv (ExplicitStratumTorus.splitting κ n I B hf hs)))).trans
    ((LinearEquiv.prodAssoc (ZMod 2) (I → ZMod 2) (I → ZMod 2)
      (Fin (ExplicitStratumTorus.torusRank κ n I B) → ZMod 2)).symm.trans
      ((LinearEquiv.sumArrowLequivProdArrow I I (ZMod 2) (ZMod 2)).symm.prodCongr
        (LinearEquiv.refl _ _)))

theorem splitting_relation
    (hz : ∀ i j : I, B (Sum.inl j.val) (Sum.inl i.val)=0) (x : (I ⊕ I) → ZMod 2) :
    splitting κ n I B hf hs (relationMap (fun a v => B a (Sum.inl v)) I x) = (x,0) := by
  dsimp only [splitting,LinearEquiv.trans_apply]
  rw [splitBits_relation κ n I B hz]
  simp only [LinearEquiv.prodCongr_apply,LinearEquiv.refl_apply]
  rw [IntegerReductionEquiv.productEquiv_column _ _
    (ExplicitStratumTorus.splitting_column κ n I B hf hs)]
  apply Prod.ext
  · funext i
    cases i <;> rfl
  · rfl

#print axioms splitBits
#print axioms splitBits_apply
#print axioms splitBits_relation
#print axioms splitting
#print axioms splitting_relation
end Verification.OriginalWittCharacterSplitting
