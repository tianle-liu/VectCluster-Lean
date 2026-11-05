/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BinarySignedFiberCoordinates

/-!
# Binary Coordinate Split

A literal coordinate embedding splits a binary coordinate space into
its selected coordinates and the actual complementary coordinates.
-/
noncomputable section
open scoped Classical
namespace Verification.BinaryCoordinateSplit
variable {ι α : Type*} (f : ι → α) (hf : Function.Injective f)

abbrev Complement := {a : α // a ∉ Set.range f}

def indexEquiv : (ι ⊕ Complement f) ≃ α :=
  (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range f))

theorem index_left (i : ι) : indexEquiv f hf (Sum.inl i) = f i := rfl

theorem index_right (a : Complement f) : indexEquiv f hf (Sum.inr a) = a.val := rfl

def equiv : (α → ZMod 2) ≃ₗ[ZMod 2] ((ι → ZMod 2) × (Complement f → ZMod 2)) :=
  (LinearEquiv.piCongrLeft' (ZMod 2) (fun _ => ZMod 2) (indexEquiv f hf).symm).trans
    (LinearEquiv.sumArrowLequivProdArrow ι (Complement f) (ZMod 2) (ZMod 2))

theorem left (x : α → ZMod 2) (i : ι) : (equiv f hf x).1 i = x (f i) := rfl

theorem right (x : α → ZMod 2) (a : Complement f) : (equiv f hf x).2 a = x a.val := rfl

theorem single (i : ι) : equiv f hf (Pi.single (f i) 1) = (Pi.single i 1,0) := by
  apply Prod.ext
  · funext j
    rw [left]
    simp [Pi.single_apply,hf.eq_iff]
  · funext a
    rw [right]
    have h : a.val ≠ f i := fun he => a.property ⟨i,he.symm⟩
    simp [Pi.single_apply,h,Ne.symm h]

theorem outside_single (a : Complement f) :
    equiv f hf (Pi.single a.val 1) = (0,Pi.single a 1) := by
  apply Prod.ext
  · funext i
    rw [left]
    have h : f i ≠ a.val := fun he => a.property ⟨i,he⟩
    simp [Pi.single_apply,h,Ne.symm h]
  · funext b
    rw [right]
    simp [Pi.single_apply,Subtype.ext_iff]

#print axioms Complement
#print axioms indexEquiv
#print axioms index_left
#print axioms index_right
#print axioms equiv
#print axioms left
#print axioms right
#print axioms single
#print axioms outside_single
end Verification.BinaryCoordinateSplit
