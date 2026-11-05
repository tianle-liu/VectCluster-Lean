/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SignedGroupRingFace

/-!
# Signed Projection Products

Coordinate projection commutes with products of signed characters in
its kernel. These are the ordinary product rules needed for Pfister words.
-/
noncomputable section
open scoped Classical BigOperators
namespace Verification.SignedProjectionProducts
open MonoidAlgebra Verification.SignedGroupRingFace
variable {G H : Type*} [CommGroup G] [Group H] (χ : G →* H)

theorem one_zero : projection χ (1 : RingOf G) = 0 := by
  have hh := projection_single χ (1 : G) 1
  simpa [weight,map_one] using hh

theorem character (g : G) (h : χ g ≠ 1) : projection χ (of ℤ G g) = of ℤ G g := by
  simpa [MonoidAlgebra.of_apply,weight,h] using projection_single χ g 1

theorem signed_factor (g : G) (hg : χ g = 1) (s : ℤ) (a : RingOf G) :
    projection χ (a * (s • of ℤ G g - 1)) = projection χ a * (s • of ℤ G g - 1) := by
  rw [mul_sub,mul_smul_comm,mul_one,map_sub,map_smul,projection_shift χ g hg]
  rw [mul_sub,mul_smul_comm,mul_one]

theorem signed_product {ι : Type*} (S : Finset ι) (g : ι → G) (s : ι → ℤ)
    (hg : ∀ i ∈ S, χ (g i) = 1) (a : RingOf G) :
    projection χ (a * ∏ i ∈ S, (s i • of ℤ G (g i) - 1)) =
      projection χ a * ∏ i ∈ S, (s i • of ℤ G (g i) - 1) := by
  induction S using Finset.induction_on generalizing a with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,← mul_assoc,ih (fun j hj => hg j (Finset.mem_insert_of_mem hj)),
      signed_factor χ (g i) (hg i (Finset.mem_insert_self _ _)) (s i),mul_assoc]

theorem signed_product_zero {ι : Type*} (S : Finset ι) (g : ι → G) (s : ι → ℤ)
    (hg : ∀ i ∈ S, χ (g i) = 1) :
    projection χ (∏ i ∈ S, (s i • of ℤ G (g i) - 1)) = 0 := by
  have h := signed_product χ S g s hg (1 : RingOf G)
  simpa [one_zero] using h

#print axioms one_zero
#print axioms character
#print axioms signed_factor
#print axioms signed_product
#print axioms signed_product_zero
end Verification.SignedProjectionProducts
