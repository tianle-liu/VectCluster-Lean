/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RealCharacterFibers
import Verification.RealBitSigns
import Verification.ActualSignLabels

/-!
# Real Sign Strata

Actual real equations chi_i=-1 on each of the manuscript's allowed
F₂ labels, including the affine stratum factor.
-/
noncomputable section
namespace Verification.RealSignStrata
open Verification.RealOrthants Verification.RealCharacterFibers
variable {ι κ : Type*} [Fintype κ]

def bits (ε : κ → ZMod 2) : κ → Bool := fun a => decide (ε a=1)

theorem sign_of_bit (x : ZMod 2) : sign (decide (x=1))=(Verification.RealBitSigns.unit x : ℝ) := by
  fin_cases x <;> norm_num [sign,Verification.RealBitSigns.unit]

theorem signCharacter_negative (B : κ → ι → ℤ) (ε : κ → ZMod 2)
    (hε : ∀ i, ∑ a, (B a i : ZMod 2)*ε a=1) (i : ι) :
    signCharacter (bits ε) (fun a => B a i) = -1 := by
  unfold signCharacter bits
  simp_rw [sign_of_bit]
  exact (Verification.RealBitSigns.monomial_negative_iff (fun a => B a i) ε).mpr (hε i)

def negativeFiber (B : κ → ι → ℤ) (ε : κ → ZMod 2) :=
  {x : orthant (bits ε) // ∀ i, (∏ a, x.val a^B a i) = -1}

instance negativeFiberTopology (B : κ → ι → ℤ) (ε : κ → ZMod 2) :
    TopologicalSpace (negativeFiber B ε) := inferInstanceAs
      (TopologicalSpace {x : orthant (bits ε) // ∀ i, (∏ a, x.val a^B a i) = -1})

def signFiberEquiv (B : κ → ι → ℤ) (ε : κ → ZMod 2)
    (hε : ∀ i, ∑ a, (B a i : ZMod 2)*ε a=1) :
    negativeFiber B ε ≃ₜ fiber (bits ε) B := by
  apply (Homeomorph.refl (orthant (bits ε))).subtype
  intro x
  exact forall_congr' (fun i => by simp only [signCharacter_negative B ε hε i,Homeomorph.refl_apply,id_eq])

def coordinates (B : κ → ι → ℤ) (ε : κ → ZMod 2)
    (hε : ∀ i, ∑ a, (B a i : ZMod 2)*ε a=1) :
    negativeFiber B ε ≃ₜ LinearMap.ker (logarithmicMap B) :=
  (signFiberEquiv B ε hε).trans (Verification.RealCharacterFibers.coordinates (bits ε) B)

theorem contractible (B : κ → ι → ℤ) (ε : κ → ZMod 2)
    (hε : ∀ i, ∑ a, (B a i : ZMod 2)*ε a=1) : ContractibleSpace (negativeFiber B ε) :=
  (coordinates B ε hε).contractibleSpace

theorem nonempty (B : κ → ι → ℤ) (ε : κ → ZMod 2)
    (hε : ∀ i, ∑ a, (B a i : ZMod 2)*ε a=1) : Nonempty (negativeFiber B ε) :=
  ⟨(coordinates B ε hε).symm 0⟩

theorem affine_contractible (α : Type*) (B : κ → ι → ℤ) (ε : κ → ZMod 2)
    (hε : ∀ i, ∑ a, (B a i : ZMod 2)*ε a=1) :
    ContractibleSpace ((α → ℝ) × negativeFiber B ε) :=
  ((Homeomorph.refl (α → ℝ)).prodCongr (coordinates B ε hε)).contractibleSpace

variable {V C : Type*} [Fintype V] [Fintype C]

theorem actual_stratum_piece_contractible (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (ε : Verification.ActualSignLabels.labels B I) :
    ContractibleSpace ((I → ℝ) × negativeFiber
      (fun (a : Verification.AnticliqueSubcolumns.Rows (C := C) I) (i : I) => B a.val i.val) ε.val) :=
  affine_contractible I _ ε.val ε.property

#print axioms bits
#print axioms sign_of_bit
#print axioms signCharacter_negative
#print axioms negativeFiber
#print axioms negativeFiberTopology
#print axioms signFiberEquiv
#print axioms coordinates
#print axioms contractible
#print axioms nonempty
#print axioms affine_contractible
#print axioms actual_stratum_piece_contractible
end Verification.RealSignStrata
