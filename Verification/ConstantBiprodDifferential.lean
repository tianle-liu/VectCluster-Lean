/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WeightedConstantTerms

/-!
# Constant Biprod Differential

A constant complex contributes no differential, so every differential
of its biproduct factors through the other summand.
-/
set_option quotPrecheck false
namespace Verification.ConstantBiprodDifferential
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable (Z : C) (K : CochainComplex C ℤ)
local notation "S" => (single C (ComplexShape.up ℤ) 0).obj Z

theorem factor (p q : ℤ) : (S ⊞ K).d p q=
    (biprod.snd : S ⊞ K ⟶ K).f p ≫ K.d p q ≫ (biprod.inr : K ⟶ S ⊞ K).f q := by
  have hi := congrArg (fun f : S ⊞ K ⟶ S ⊞ K => f.f q) (biprod.total (X:=S) (Y:=K))
  simp only [add_f_apply,comp_f,id_f] at hi
  calc
    _ = (S ⊞ K).d p q ≫ ((biprod.fst : S ⊞ K ⟶ S).f q ≫ (biprod.inl : S ⟶ S ⊞ K).f q+
        (biprod.snd : S ⊞ K ⟶ K).f q ≫ (biprod.inr : K ⟶ S ⊞ K).f q) := by rw [hi,Category.comp_id]
    _ = _ := by
      rw [Preadditive.comp_add,←Category.assoc,←Category.assoc,
        ← (biprod.fst : S ⊞ K ⟶ S).comm p q,← (biprod.snd : S ⊞ K ⟶ K).comm p q]
      simp [single_obj_d,Category.assoc]

#print axioms factor
end Verification.ConstantBiprodDifferential
