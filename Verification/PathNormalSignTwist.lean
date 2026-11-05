/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCochains

/-!
# Path Normal Sign Twist

Explicit change from the original x normal frame to signed path z normal
frames. Arbitrary vertex weights are allowed; the manuscript uses w(j)=j/2.
The stratum factors and the conjugacy of every actual-shaped finite row are
proved by the literal insertion formula, including all rho terms.
-/
noncomputable section
namespace Verification.PathNormalSignTwist
open Classical Verification.PathCochains Verification.PathRhoConfiguration
variable {R : Type*} [CommRing R] (g : R) (w : ℕ → ℕ)

def factor (I : Finset ℕ) : R := ∏ i ∈ I,g^(w i)

theorem factor_insert (I : Finset ℕ) (j : ℕ) (hj : j∉I) :
    factor g w (insert j I)=g^(w j)*factor g w I := Finset.prod_insert hj

theorem factor_square (hg : g*g=1) (I : Finset ℕ) : factor g w I * factor g w I = 1 := by
  unfold factor
  rw [← Finset.prod_mul_distrib]
  simp only [← mul_pow,hg,one_pow,Finset.prod_const_one]

def twist (n : ℕ) : Total (R := R) n →ₗ[R] Total (R := R) n :=
  LinearMap.pi (fun I => factor g w I.val • LinearMap.proj I)

theorem twist_square (hg : g*g=1) (n : ℕ) : (twist g w n).comp (twist g w n)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext I
  change factor g w I.val • (factor g w I.val • x I)=x I
  rw [smul_smul,factor_square g w hg,one_smul]

def twistEquiv (hg : g*g=1) (n : ℕ) : Total (R := R) n ≃ₗ[R] Total (R := R) n :=
  LinearEquiv.ofLinear (twist g w n) (twist g w n) (twist_square g w hg n) (twist_square g w hg n)

theorem face (ρ : R) (I : Finset ℕ) (j : ℕ) (hj : j∉I) (x : List Bool →₀ R) :
    g^(w j) • faceMap g ρ I j (factor g w I • x) =
      factor g w (insert j I) • faceMap g ρ I j x := by
  rw [map_smul,smul_smul,factor_insert g w I j hj]

theorem row (ρ : R) (n : ℕ) (x : Total (R := R) n) (J : Config n) :
    (∑ j ∈ J.val,g^(w j) • faceMap g ρ (eraseConfig J j).val j
      ((twist g w n x (eraseConfig J j)).val)) =
    factor g w J.val • (differential g ρ n x J).val := by
  change (∑ j ∈ J.val,g^(w j) • faceMap g ρ (eraseConfig J j).val j
      (factor g w (eraseConfig J j).val • (x (eraseConfig J j)).val)) =
    factor g w J.val • ambientDifferential g ρ n (inclusion n x) J
  rw [ambientDifferential_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [face g w ρ (eraseConfig J j).val j (Finset.not_mem_erase j J.val)]
  rw [show insert j (eraseConfig J j).val=J.val from Finset.insert_erase hj]
  rfl

#print axioms factor
#print axioms factor_insert
#print axioms factor_square
#print axioms twist
#print axioms twist_square
#print axioms twistEquiv
#print axioms face
#print axioms row
end Verification.PathNormalSignTwist
