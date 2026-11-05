/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimitiveCharacters
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Split Scalar Characters

A split integer column map lifts arbitrary unit ratios by an explicit
character. The resulting constants satisfy the two positive/negative monomial
balance equations simultaneously; only integer powers are used.
-/
noncomputable section
namespace Verification.SplitScalarCharacters
open scoped BigOperators
open Classical
variable {R ρ σ : Type*} [CommRing R] [Fintype ρ] [Fintype σ]
variable (B : Matrix ρ σ ℤ) (L : (ρ → ℤ) →ₗ[ℤ] (σ → ℤ))
variable (hL : L.comp B.mulVecLin=LinearMap.id) (a b : σ → Rˣ)

def character : Multiplicative (ρ → ℤ) →* Rˣ :=
  (PrimitiveCharacters.basisCharacter (Pi.basisFun ℤ σ) (fun i=>b i/a i)).comp
    L.toAddMonoidHom.toMultiplicative

def constants (r : ρ) : Rˣ := character L a b (Multiplicative.ofAdd (Pi.single r 1))

omit [Fintype σ] in
theorem character_product (χ : Multiplicative (ρ → ℤ) →* Rˣ) (x : ρ → ℤ) :
    χ (Multiplicative.ofAdd x)=∏ r,χ (Multiplicative.ofAdd (Pi.single r 1))^x r := by
  have hx : x=∑ r,x r • (Pi.single r (1:ℤ) : ρ → ℤ) := by
    simpa only [Pi.basisFun_repr,Pi.basisFun_apply] using ((Pi.basisFun ℤ ρ).sum_repr x).symm
  conv_lhs => rw [hx]
  rw [ofAdd_sum,map_prod]
  apply Finset.prod_congr rfl
  intro r _
  rw [ofAdd_zsmul,map_zpow]

include hL in
omit [Fintype ρ] in
theorem column_character (i : σ) : character L a b (Multiplicative.ofAdd (fun r=>B r i))=b i/a i := by
  have h := LinearMap.congr_fun hL (Pi.single i 1)
  have hb : B.mulVec (Pi.single i 1)=fun r=>B r i := by
    exact Matrix.mulVec_single_one B i
  change L (B.mulVec (Pi.single i 1))=Pi.single i 1 at h
  rw [hb] at h
  change PrimitiveCharacters.basisCharacter (Pi.basisFun ℤ σ) (fun i=>b i/a i)
    (Multiplicative.ofAdd (L (fun r=>B r i)))=_
  rw [h]
  exact PrimitiveCharacters.basisCharacter_apply (Pi.basisFun ℤ σ) (fun i=>b i/a i) i

include hL in
theorem constants_ratio (i : σ) : ∏ r,constants L a b r^B r i=b i/a i := by
  unfold constants
  rw [← character_product]
  exact column_character B L hL a b i

omit [Fintype ρ] [Fintype σ] in
theorem positive_div_negative (z : ℤ) (u : Rˣ) : u^z.toNat/u^(-z).toNat=u^z := by
  cases z with
  | ofNat n => simp
  | negSucc n => simp [Int.neg_negSucc,zpow_negSucc]

include hL in
theorem balance (i : σ) : a i*∏ r,constants L a b r^(B r i).toNat=
    b i*∏ r,constants L a b r^(-B r i).toNat := by
  have h := constants_ratio B L hL a b i
  have hp : (∏ r,constants L a b r^(B r i).toNat)/
      (∏ r,constants L a b r^(-B r i).toNat)=b i/a i := by
    rw [← Finset.prod_div_distrib]
    simpa only [positive_div_negative] using h
  have hh:= (div_eq_div_iff_mul_eq_mul).mp hp
  simpa only [mul_comm] using hh

#print axioms character
#print axioms constants
#print axioms character_product
#print axioms column_character
#print axioms constants_ratio
#print axioms positive_div_negative
#print axioms balance
end Verification.SplitScalarCharacters
