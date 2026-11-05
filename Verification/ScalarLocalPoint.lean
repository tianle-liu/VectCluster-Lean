/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarLocalSmooth

/-!
# Scalar Local Point

An AS scalar chart has a point over its coefficient ring with every
selected original and mutated coordinate zero. This proves nonemptiness
of its actual zero layer over a nonzero coefficient ring.
-/
noncomputable section
universe u
namespace Verification.ScalarLocalPoint
open Verification.ScalarLocalSmooth Verification.LocalExchangeSmooth Verification.CharacterMapSmooth
variable {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module.Finite ℤ M]
variable (f : (ι →₀ ℤ) →ₗ[ℤ] M) (c : ι → Rˣ)
variable (hf : Function.Injective f) (hs : FreezingLattice.Saturated (LinearMap.range f))
include hf hs

theorem coefficient_point : ∃ p : Torus R M →ₐ[R] R,
    ∀ i, p (scaledCharacters f c i : Torus R M) = -1 := by
  obtain ⟨d,hd⟩ := TorusTranslation.primitive_character_extension f hf hs
    (PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne (fun i => -(c i)⁻¹))
  let p : Torus R M →ₐ[R] R := MonoidAlgebra.lift R _ _ ((Units.coeHom R).comp d)
  refine ⟨p,fun i => ?_⟩
  have hi := hd (Finsupp.basisSingleOne i)
  rw [PrimitiveCharacters.basisCharacter_apply] at hi
  change p (algebraMap R _ (c i : R) *
    MonoidAlgebra.of R (Multiplicative M) (Multiplicative.ofAdd (f (Finsupp.single i 1)))) = -1
  rw [map_mul,AlgHom.commutes]
  simp only [p,MonoidAlgebra.lift_of, RingHom.id_apply, MonoidHom.comp_apply, Units.coeHom_apply]
  change (c i : R) * (d (Multiplicative.ofAdd (f (Finsupp.basisSingleOne i))) : Rˣ) = -1
  rw [hi]
  simp

theorem zero_point : ∃ p : LocalAlgebra (scaledCharacters f c) →ₐ[R] R,
    (∀ i, p (x (scaledCharacters f c) i) = 0) ∧
    (∀ i, p (y (scaledCharacters f c) i) = 0) := by
  obtain ⟨p,hp⟩ := coefficient_point f c hf hs
  let q := lift (scaledCharacters f c) p (fun _ => 0) (fun _ => 0)
    (fun i => by rw [zero_mul,zero_sub,hp])
  exact ⟨q,fun i => lift_x _ _ _ _ _ i,fun i => lift_y _ _ _ _ _ i⟩

#print axioms coefficient_point
#print axioms zero_point
end Verification.ScalarLocalPoint
