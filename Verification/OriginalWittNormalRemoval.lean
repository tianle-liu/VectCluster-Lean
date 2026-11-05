/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittOriginalExponent
import Verification.SquareClassCharacter

/-!
# Original Witt Normal Removal

The normal bits of every group-ring monomial disappear in the actual
signed quotient because the defining relations set their characters to 1.
-/
noncomputable section
open scoped Classical
namespace Verification.OriginalWittNormalRemoval
open Verification.OriginalWittQuotient Verification.OriginalWittCharacterSplitting
open Verification.IndependentChartIndex
variable (κ : Type) [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def normalInclusion : Multiplicative (I → ZMod 2) →* Group (Fin n) κ :=
  (((splitBits κ n I).symm.toLinearMap.comp
    (LinearMap.inl (ZMod 2) (I → ZMod 2) ((Other n I ⊕ κ) → ZMod 2))).toAddMonoidHom.toMultiplicative)

omit [Fintype κ] in
theorem normal_single (i : I) : normalInclusion κ n I (Multiplicative.ofAdd (Pi.single i 1)) =
    normalVector (C := κ) i.val := by
  apply Multiplicative.toAdd.injective
  apply (splitBits κ n I).injective
  change splitBits κ n I ((splitBits κ n I).symm (Pi.single i 1,0)) = _
  rw [LinearEquiv.apply_symm_apply,splitBits_apply]
  apply Prod.ext
  · funext j
    simp [normalVector,Pi.single_apply,Subtype.val_inj]
  · funext j
    have hj : (originals κ n I).symm (Sum.inr j) ≠ Sum.inl i.val := by
      intro h
      have hh := congrArg (originals κ n I) h
      rw [Equiv.apply_symm_apply] at hh
      have hi : originals κ n I (Sum.inl i.val) = Sum.inl i :=
        (originals κ n I).apply_symm_apply (Sum.inl i)
      rw [hi] at hh
      cases hh
    simp [normalVector,Pi.single_apply,hj]

def quotientCharacter : Group (Fin n) κ →* Stratum (fun a v => B a (Sum.inl v)) I :=
  (Ideal.Quotient.mk (relationIdeal (fun a v => B a (Sum.inl v)) I)).toMonoidHom.comp
    (MonoidAlgebra.of ℤ _)

omit [Fintype κ] in
theorem normal_trivial : (quotientCharacter κ n I B).comp (normalInclusion κ n I) = 1 := by
  have hn (i : I) : quotientCharacter κ n I B
      (normalInclusion κ n I (Multiplicative.ofAdd (Pi.single i 1))) = 1 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr
      (normal_relation (fun a v => B a (Sum.inl v)) I i)
    have hr : quotientCharacter κ n I B (normalVector i.val) = 1 := by
      simpa only [quotientCharacter,MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_coe,map_sub,map_one,sub_eq_zero] using h
    exact (congrArg (quotientCharacter κ n I B) (normal_single κ n I i)).trans hr
  apply MonoidHom.ext
  intro a
  have ha : a = ∏ i, (Multiplicative.ofAdd (Pi.single i (1:ZMod 2))) ^
      (Multiplicative.toAdd a i).val := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_prod,toAdd_pow,toAdd_ofAdd]
    funext j
    simp only [Finset.sum_apply,Pi.smul_apply]
    simp [Pi.single_apply,nsmul_eq_mul]
  rw [ha]
  simp only [MonoidHom.comp_apply,map_prod,map_pow,hn,one_pow,Finset.prod_const_one,MonoidHom.one_apply]

def remove (a : Bits (Fin n) κ) : Bits (Fin n) κ :=
  (splitBits κ n I).symm (0,(splitBits κ n I a).2)

omit [Fintype κ] in
theorem quotient_remove (a : Bits (Fin n) κ) :
    quotientCharacter κ n I B (Multiplicative.ofAdd a) =
      quotientCharacter κ n I B (Multiplicative.ofAdd (remove κ n I a)) := by
  have hd : Multiplicative.ofAdd a =
      normalInclusion κ n I (Multiplicative.ofAdd (splitBits κ n I a).1) *
        Multiplicative.ofAdd (remove κ n I a) := by
    apply Multiplicative.toAdd.injective
    apply (splitBits κ n I).injective
    change splitBits κ n I a = splitBits κ n I
      ((splitBits κ n I).symm ((splitBits κ n I a).1,0) +
        (splitBits κ n I).symm (0,(splitBits κ n I a).2))
    rw [map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    simp
  rw [hd,map_mul]
  have hn := DFunLike.congr_fun (normal_trivial κ n I B)
    (Multiplicative.ofAdd (splitBits κ n I a).1)
  change quotientCharacter κ n I B (normalInclusion κ n I _) = 1 at hn
  rw [hn,one_mul]

def integerOutside (a : Bits (Fin n) κ) : (Other n I ⊕ κ) →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (fun i => ((splitBits κ n I a).2 i).val)

theorem exponent_integerOutside (a : Bits (Fin n) κ) :
    OriginalWittOutsideBits.exponent κ n I (integerOutside κ n I a) = remove κ n I a := by
  apply (splitBits κ n I).injective
  rw [OriginalWittOutsideBits.exponent,remove,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · rfl
  · funext i
    simp [integerOutside]

#print axioms normalInclusion
#print axioms normal_single
#print axioms quotientCharacter
#print axioms normal_trivial
#print axioms remove
#print axioms quotient_remove
#print axioms integerOutside
#print axioms exponent_integerOutside
end Verification.OriginalWittNormalRemoval
