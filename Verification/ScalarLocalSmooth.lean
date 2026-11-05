/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalExchangeTransport
import Verification.TorusTranslation
import Verification.SaturatedSmith

/-!
# Scalar Local Smooth

Primitive characters with arbitrary unit constants give actual smooth
local exchange rings. Translation preserves every x and y coordinate, so
the original-coordinate parameter morphism is smooth as well.
-/
noncomputable section
universe u
namespace Verification.ScalarLocalSmooth
open Verification.LocalExchangeSmooth Verification.CharacterMapSmooth
variable {R M ι : Type u} [CommRing R] [AddCommGroup M]
variable (f : (ι →₀ ℤ) →ₗ[ℤ] M) (c : ι → Rˣ)

def scaledCharacters (i : ι) : (Torus R M)ˣ :=
  Units.map (algebraMap R (Torus R M)).toMonoidHom (c i) * characterUnits R f i

variable [Module.Finite ℤ M]

theorem translation_exists (hf : Function.Injective f)
    (hs : FreezingLattice.Saturated (LinearMap.range f)) :
    ∃ e : Torus R M ≃ₐ[R] Torus R M,
      ∀ i, e (characterUnits R f i : Torus R M) = (scaledCharacters f c i : Torus R M) := by
  obtain ⟨e,he⟩ := TorusTranslation.primitive_translation f hf hs
    (PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne c)
  refine ⟨e,fun i => ?_⟩
  have h := he (Finsupp.basisSingleOne i)
  rw [PrimitiveCharacters.basisCharacter_apply] at h
  exact h

variable [Fintype ι]

theorem local_smooth_saturated {δ : Type u} [Fintype δ]
    (bM : Basis δ ℤ M) (hf : Function.Injective f)
    (hs : FreezingLattice.Saturated (LinearMap.range f)) :
    Algebra.Smooth R (LocalAlgebra (scaledCharacters f c)) := by
  obtain ⟨n,s⟩ := (LinearMap.range f).smithNormalForm bM
  obtain ⟨e,he⟩ := translation_exists f c hf hs
  letI := local_character_smooth (R := R) f hf s (fun i => by
    simp only [SaturatedSmith.coefficient_natAbs s hs, Nat.cast_one, isUnit_one])
  exact Algebra.Smooth.of_equiv (LocalExchangeTransport.localEquiv e
    (characterUnits R f) (scaledCharacters f c) he)

theorem parameters_smooth_saturated {δ : Type u} [Fintype δ]
    (bM : Basis δ ℤ M) (hf : Function.Injective f)
    (hs : FreezingLattice.Saturated (LinearMap.range f)) :
    Algebra.Smooth (MvPolynomial ι R) (LocalAlgebra (scaledCharacters f c)) := by
  obtain ⟨n,s⟩ := (LinearMap.range f).smithNormalForm bM
  obtain ⟨e,he⟩ := translation_exists f c hf hs
  letI := LocalExchangeParameters.local_character_parameters_smooth (R := R) f hf s (fun i => by
    simp only [SaturatedSmith.coefficient_natAbs s hs, Nat.cast_one, isUnit_one])
  exact Algebra.Smooth.of_equiv (LocalExchangeTransport.parameterEquiv e
    (characterUnits R f) (scaledCharacters f c) he)

#print axioms scaledCharacters
#print axioms translation_exists
#print axioms local_smooth_saturated
#print axioms parameters_smooth_saturated
end Verification.ScalarLocalSmooth
