/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RealOrthants
import Mathlib.LinearAlgebra.Pi

/-!
# Real Character Fibers

On each sign orthant, the literal real character equations become a
linear kernel under log absolute values. Thus every nonempty sign fiber,
including its affine factor, is contractible.
-/
noncomputable section
namespace Verification.RealCharacterFibers
open Verification.RealOrthants
variable {ι κ : Type*} [Fintype κ]

def sign (b : Bool) : ℝ := if b then -1 else 1

theorem sign_ne_zero (b : Bool) : sign b ≠ 0 := by cases b <;> simp [sign]

theorem signedExp_factor (b : Bool) (t : ℝ) : signedExp b t=sign b*Real.exp t := by
  cases b <;> simp [signedExp,sign]

theorem exp_integer_mul (t : ℝ) (n : ℤ) : Real.exp ((n:ℝ)*t)=(Real.exp t)^n := by
  calc Real.exp ((n:ℝ)*t) = Real.exp (Real.log ((Real.exp t)^n)) := by
         rw [Real.log_zpow,Real.log_exp]
       _ = (Real.exp t)^n := Real.exp_log (zpow_pos (Real.exp_pos t) n)

def signCharacter (σ : κ → Bool) (v : κ → ℤ) : ℝ := ∏ a, sign (σ a)^v a

theorem signCharacter_ne_zero (σ : κ → Bool) (v : κ → ℤ) : signCharacter σ v ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  exact zpow_ne_zero _ (sign_ne_zero (σ a))

theorem character_signedExp (σ : κ → Bool) (v : κ → ℤ) (t : κ → ℝ) :
    (∏ a, signedExp (σ a) (t a)^v a)=
      signCharacter σ v * Real.exp (∑ a, (v a:ℝ)*t a) := by
  simp only [signedExp_factor,mul_zpow,Finset.prod_mul_distrib,signCharacter,
    Real.exp_sum,exp_integer_mul]

theorem character_log (σ : κ → Bool) (v : κ → ℤ) (x : orthant σ) :
    (∏ a, x.val a^v a)=signCharacter σ v * Real.exp (∑ a, (v a:ℝ)*Real.log (x.val a)) := by
  have h := character_signedExp σ v (fun a => Real.log (x.val a))
  simpa only [signedExp_log _ _ (x.property _)] using h

theorem character_eq_sign_iff (σ : κ → Bool) (v : κ → ℤ) (x : orthant σ) :
    (∏ a, x.val a^v a)=signCharacter σ v ↔ ∑ a, (v a:ℝ)*Real.log (x.val a)=0 := by
  rw [character_log]
  conv_lhs => rhs; rw [← mul_one (signCharacter σ v)]
  constructor
  · intro h
    have hh := mul_left_cancel₀ (signCharacter_ne_zero σ v) h
    simpa using hh
  · intro h
    rw [h,Real.exp_zero]

def logarithmicMap (B : κ → ι → ℤ) : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun t i := ∑ a, (B a i:ℝ)*t a
  map_add' t u := by funext i; simp [mul_add,Finset.sum_add_distrib]
  map_smul' r t := by
    funext i
    simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro a _
    ring

def fiber (σ : κ → Bool) (B : κ → ι → ℤ) :=
  {x : orthant σ // ∀ i, (∏ a, x.val a^B a i)=signCharacter σ (fun a => B a i)}

instance fiberTopology (σ : κ → Bool) (B : κ → ι → ℤ) : TopologicalSpace (fiber σ B) :=
  inferInstanceAs (TopologicalSpace {x : orthant σ //
    ∀ i, (∏ a, x.val a^B a i)=signCharacter σ (fun a => B a i)})

def coordinates (σ : κ → Bool) (B : κ → ι → ℤ) :
    fiber σ B ≃ₜ LinearMap.ker (logarithmicMap B) := by
  apply (logCoordinates σ).subtype
  intro x
  simp only [LinearMap.mem_ker,funext_iff,Pi.zero_apply,logarithmicMap,
    LinearMap.coe_mk,AddHom.coe_mk,logCoordinates]
  exact forall_congr' (fun i => character_eq_sign_iff σ (fun a => B a i) x)

theorem contractible (σ : κ → Bool) (B : κ → ι → ℤ) : ContractibleSpace (fiber σ B) :=
  (coordinates σ B).contractibleSpace

def affineCoordinates (α : Type*) (σ : κ → Bool) (B : κ → ι → ℤ) :
    ((α → ℝ) × fiber σ B) ≃ₜ ((α → ℝ) × LinearMap.ker (logarithmicMap B)) :=
  (Homeomorph.refl _).prodCongr (coordinates σ B)

theorem affine_contractible (α : Type*) (σ : κ → Bool) (B : κ → ι → ℤ) :
    ContractibleSpace ((α → ℝ) × fiber σ B) := (affineCoordinates α σ B).contractibleSpace

#print axioms sign
#print axioms sign_ne_zero
#print axioms signedExp_factor
#print axioms exp_integer_mul
#print axioms signCharacter
#print axioms signCharacter_ne_zero
#print axioms character_signedExp
#print axioms character_log
#print axioms character_eq_sign_iff
#print axioms logarithmicMap
#print axioms fiber
#print axioms fiberTopology
#print axioms coordinates
#print axioms contractible
#print axioms affineCoordinates
#print axioms affine_contractible
end Verification.RealCharacterFibers
