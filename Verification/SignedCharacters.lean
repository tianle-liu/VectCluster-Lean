/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmithCharacters
import Mathlib.Algebra.Ring.Commute

/-!
# Signed Characters

Constants in Smith coordinates for the article's character fiber.
Changing the lattice basis preserves order two; hence the transformed
right-hand sides over a field are still precisely signs.
-/
namespace Verification.SignedCharacters
open Verification.PrimitiveCharacters Verification.SmithCharacters
variable {R P M ι κ : Type*} [CommRing R] [AddCommGroup P] [AddCommGroup M]

theorem basisCharacter_sq_one (b : Basis κ ℤ P) (u : κ → Rˣ)
    (hu : ∀ i, u i ^ 2 = 1) (x : Multiplicative P) :
    basisCharacter b u x ^ 2 = 1 := by
  have hx : x ∈ Subgroup.closure (Set.range (fun i => Multiplicative.ofAdd (b i))) := by
    rw [basis_generates]
    trivial
  refine Subgroup.closure_induction (fun y hy => ?_) ?_
    (fun a d _ _ ha hd => ?_) (fun a _ ha => ?_) hx
  · obtain ⟨i,rfl⟩ := hy
    simpa only [basisCharacter_apply] using hu i
  · simp
  · rw [map_mul, mul_pow, ha, hd, mul_one]
  · rw [map_inv, inv_pow, ha, inv_one]

theorem negative_character_sq_one (b : Basis κ ℤ P) (x : Multiplicative P) :
    basisCharacter b (fun _ => (-1 : Rˣ)) x ^ 2 = 1 :=
  basisCharacter_sq_one b _ (fun _ => by simp) x

theorem smith_negative_constant_sq_one (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (b : Basis κ ℤ P) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)
    (i : Fin n) : smithConstants f hf s (basisCharacter b (fun _ => (-1 : Rˣ))) i ^ 2 = 1 :=
  negative_character_sq_one b _

theorem positive_constant_sq_one (a : ℤ) (u : Rˣ) (hu : u ^ 2 = 1) :
    positiveConstant a u ^ 2 = 1 := by
  unfold positiveConstant
  split_ifs
  · rw [inv_pow, hu, inv_one]
  · exact hu

variable {k : Type*} [Field k]

theorem smith_negative_constant_is_sign (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (b : Basis κ ℤ P) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)
    (i : Fin n) :
    (positiveConstant (s.a i)
      (smithConstants f hf s (basisCharacter b (fun _ => (-1 : kˣ))) i) : k) = 1 ∨
    (positiveConstant (s.a i)
      (smithConstants f hf s (basisCharacter b (fun _ => (-1 : kˣ))) i) : k) = -1 := by
  apply sq_eq_one_iff.mp
  have h := positive_constant_sq_one (s.a i) _
    (smith_negative_constant_sq_one (R := k) f hf b s i)
  exact congrArg (fun v : kˣ => (v : k)) h

#print axioms basisCharacter_sq_one
#print axioms negative_character_sq_one
#print axioms smith_negative_constant_sq_one
#print axioms positive_constant_sq_one
#print axioms smith_negative_constant_is_sign
end Verification.SignedCharacters
