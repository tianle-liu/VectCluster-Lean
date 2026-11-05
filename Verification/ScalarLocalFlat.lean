/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarLocalSmooth
import Verification.ActualOpenRegular

/-!
# Scalar Local Flat

The scalar AS parameter projection is flat, via a coordinate-preserving
torus translation and the proved character-map flatness theorem.
-/
noncomputable section
universe u
namespace Verification.ScalarLocalFlat
open Verification.ScalarLocalSmooth Verification.LocalExchangeSmooth
variable {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module.Finite ℤ M]
variable (f : (ι →₀ ℤ) →ₗ[ℤ] M) (c : ι → Rˣ)

theorem parameters_flat {δ : Type u} [Fintype δ] (bM : Basis δ ℤ M)
    (hf : Function.Injective f) (hs : FreezingLattice.Saturated (LinearMap.range f)) :
    Module.Flat (MvPolynomial ι R) (LocalAlgebra (scaledCharacters f c)) := by
  obtain ⟨n,s⟩ := (LinearMap.range f).smithNormalForm bM
  obtain ⟨e,he⟩ := translation_exists f c hf hs
  letI := ActualOpenRegular.local_character_parameters_flat (R := R) f hf s
  exact Module.Flat.of_linearEquiv (LocalExchangeTransport.parameterEquiv e
    (characterUnits R f) (scaledCharacters f c) he).symm.toLinearEquiv

#print axioms parameters_flat
end Verification.ScalarLocalFlat
