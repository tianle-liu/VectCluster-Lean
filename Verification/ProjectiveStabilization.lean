/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StableFree
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Projective Stabilization

The stable-freeness deduction constructs its finite free complement
from the actual finite-projective hypotheses on the stabilizing module.
-/
noncomputable section
namespace Verification.ProjectiveStabilization
variable {R M Q P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
  [AddCommGroup P] [Module R P]

def splitKernel (f : M →ₗ[R] Q) (g : Q →ₗ[R] M) (h : f.comp g = LinearMap.id) :
    M ≃ₗ[R] Q × LinearMap.ker f where
  toFun x := (f x, ⟨x - g (f x), by
    change f (x - g (f x)) = 0
    rw [map_sub, show f (g (f x)) = f x from LinearMap.congr_fun h (f x), sub_self]⟩)
  invFun y := g y.1 + y.2
  left_inv x := by simp
  right_inv y := by
    obtain ⟨q,x,hx⟩ := y
    have hg := LinearMap.congr_fun h q
    change f (g q) = q at hg
    apply Prod.ext
    · change f (g q + x) = q
      simp only [map_add, hg, show f x = 0 from hx, add_zero]
    · apply Subtype.ext
      change g q + x - g (f (g q + x)) = x
      simp only [map_add, hg, show f x = 0 from hx, add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · exact map_add f x y
    · apply Subtype.ext
      change x + y - g (f (x + y)) = (x - g (f x)) + (y - g (f y))
      simp only [map_add]
      abel
  map_smul' a x := by
    apply Prod.ext
    · exact map_smul f a x
    · apply Subtype.ext
      change a • x - g (f (a • x)) = a • (x - g (f x))
      simp only [map_smul, smul_sub]

theorem finite_projective_complement [Module.Finite R Q] [Module.Projective R Q] :
    ∃ (n : ℕ) (S : Submodule R (Fin n → R)), Nonempty ((Q × S) ≃ₗ[R] (Fin n → R)) := by
  obtain ⟨n,f,g,_,_,h⟩ := Module.Finite.exists_comp_eq_id_of_projective R Q
  exact ⟨n,LinearMap.ker f,⟨(splitKernel f g h).symm⟩⟩

theorem stable_free_of_projective_stabilizer [Module.Finite R Q] [Module.Projective R Q]
    {r : ℕ} (e : (P × Q) ≃ₗ[R] ((Fin r → R) × Q)) :
    ∃ n : ℕ, Nonempty ((P × (Fin n → R)) ≃ₗ[R] ((Fin r → R) × (Fin n → R))) := by
  obtain ⟨n,S,⟨f⟩⟩ := finite_projective_complement (R := R) (Q := Q)
  exact ⟨n,Verification.StableFree.stable_free_of_complement e f⟩

#print axioms splitKernel
#print axioms finite_projective_complement
#print axioms stable_free_of_projective_stabilizer
end Verification.ProjectiveStabilization
