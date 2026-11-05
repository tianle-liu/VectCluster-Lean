/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineSignature
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Tactic.FinCases

/-!
# Boolean Affine Lattice

Every actual affine map of finite F₂ vector spaces preserves the
signature lattices. This bridge does not assume Boolean polynomial formulas
for the map: they are derived from its affine linear structure.
-/
noncomputable section
namespace Verification.BooleanAffineLattice
open Verification.SignatureLattice Verification.AffineSignature
abbrev Bit := ZMod 2
variable {α β : Type*} [Fintype α] [DecidableEq α]

def lift (b : Bit) : ℤ := if b=0 then 0 else 1

theorem lift_add (a b : Bit) : lift (a+b)=lift a+lift b-2*(lift a*lift b) := by
  fin_cases a <;> fin_cases b <;> norm_num [lift,show (1:Bit)+1=0 from rfl]

def vector (S : Finset α) : α → Bit := fun a => if a∈S then 1 else 0

omit [Fintype α] in
theorem lift_coordinate (a : α) : (fun S => lift (vector S a))=booleanMonomial {a} := by
  funext S
  by_cases ha : a∈S <;> simp [vector,lift,booleanMonomial,ha]

theorem lift_const_mem (b : Bit) : (fun _ : Finset α => lift b) ∈ signatureLattice 1 := by
  fin_cases b
  · change (0 : Finset α → ℤ) ∈ signatureLattice 1
    exact Submodule.zero_mem _
  · simpa [lift] using (one_mem_one (α := α))

theorem lift_add_mem (f g : Finset α → Bit)
    (hf : (fun S => lift (f S)) ∈ signatureLattice 1)
    (hg : (fun S => lift (g S)) ∈ signatureLattice 1) :
    (fun S => lift (f S+g S)) ∈ signatureLattice 1 := by
  have h := xor_mem_one (fun S => lift (f S)) (fun S => lift (g S)) hf hg
  simpa only [lift_add,xorFunction,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.mul_apply,smul_eq_mul] using h

theorem lift_sum_mem {γ : Type*} (s : Finset γ) (f : γ → Finset α → Bit)
    (hf : ∀ a∈s, (fun S => lift (f a S)) ∈ signatureLattice 1) :
    (fun S => lift (∑ a∈s, f a S)) ∈ signatureLattice 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change (0 : Finset α → ℤ) ∈ signatureLattice 1
    exact Submodule.zero_mem _
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      lift_add_mem (f a) (fun S => ∑ a∈s, f a S)
        (hf a (Finset.mem_insert_self _ _)) (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

theorem linear_formula (L : (α → Bit) →ₗ[Bit] Bit) (S : Finset α) :
    L (vector S)=∑ a, vector S a*L (Pi.single a 1) := by
  have h : vector S=∑ a, vector S a • (Pi.single a 1 : α → Bit) := by
    ext b
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  conv_lhs => rw [h]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]

theorem lift_linear_mem (L : (α → Bit) →ₗ[Bit] Bit) :
    (fun S => lift (L (vector S))) ∈ signatureLattice 1 := by
  simp_rw [linear_formula]
  apply lift_sum_mem
  intro a _
  generalize L (Pi.single a 1)=b
  fin_cases b
  · change (fun S => lift (vector S a * 0)) ∈ signatureLattice 1
    simp only [mul_zero]
    change (0 : Finset α → ℤ) ∈ signatureLattice 1
    exact Submodule.zero_mem _
  · change (fun S => lift (vector S a * 1)) ∈ signatureLattice 1
    simpa only [mul_one,lift_coordinate] using coordinate_mem_one a

theorem lift_affine_mem (F : (α → Bit) →ᵃ[Bit] Bit) :
    (fun S => lift (F (vector S))) ∈ signatureLattice 1 := by
  have he (S : Finset α) : F (vector S)=F.linear (vector S)+F 0 := by
    simpa using F.map_vadd (0 : α → Bit) (vector S)
  simp_rw [he]
  exact lift_add_mem _ _ (lift_linear_mem F.linear) (lift_const_mem (F 0))

variable [Fintype β] [DecidableEq β]

def asFinset (F : (α → Bit) →ᵃ[Bit] (β → Bit)) (S : Finset α) : Finset β :=
  Finset.univ.filter (fun i => F (vector S) i=1)

omit [Fintype α] in
theorem coordinate_pullback (F : (α → Bit) →ᵃ[Bit] (β → Bit)) (i : β) :
    pullback (asFinset F) (booleanMonomial {i})=(fun S => lift (F (vector S) i)) := by
  funext S
  change (if {i}⊆asFinset F S then (1:ℤ) else 0)=_
  simp only [Finset.singleton_subset_iff,asFinset,Finset.mem_filter,Finset.mem_univ,true_and]
  generalize F (vector S) i=b
  fin_cases b <;> norm_num [lift]

theorem affine_preserves (F : (α → Bit) →ᵃ[Bit] (β → Bit)) (s : ℤ)
    (f : Finset β → ℤ) (hf : f ∈ signatureLattice s) :
    pullback (asFinset F) f ∈ signatureLattice s := by
  apply pullback_preserves (asFinset F) _ s f hf
  intro i
  rw [coordinate_pullback]
  exact lift_affine_mem ((LinearMap.proj i).toAffineMap.comp F)

#print axioms Bit
#print axioms lift
#print axioms lift_add
#print axioms vector
#print axioms lift_coordinate
#print axioms lift_const_mem
#print axioms lift_add_mem
#print axioms lift_sum_mem
#print axioms linear_formula
#print axioms lift_linear_mem
#print axioms lift_affine_mem
#print axioms asFinset
#print axioms coordinate_pullback
#print axioms affine_preserves
end Verification.BooleanAffineLattice
