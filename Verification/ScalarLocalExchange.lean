/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TorusTranslation
import Verification.LocalCoefficientChange
import Verification.SaturatedSmith
import Verification.ActualOpenRegular

/-!
# Scalar Local Exchange

Nonzero scalar factors in the actual local exchange quotient are
removed by a torus translation for primitive independent columns. The
equivalence fixes all original x and mutated y coordinates.
-/
noncomputable section
universe u
namespace Verification.ScalarLocalExchange
open Verification.LocalExchangeSmooth Verification.CharacterMapSmooth
open Verification.PrimitiveCharacters Verification.LocalExchangeParameters
variable {R M ι β : Type u} [CommRing R] [AddCommGroup M]

def scalarUnits (f : (ι →₀ ℤ) →ₗ[ℤ] M) (c : ι → Rˣ) (i : ι) : (Torus R M)ˣ :=
  Units.map (algebraMap R (Torus R M)).toMonoidHom (c i) * characterUnits R f i

theorem exists_coefficient_translation [Module.Finite ℤ M]
    (f : (ι →₀ ℤ) →ₗ[ℤ] M) (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) (c : ι → Rˣ) :
    ∃ e : Torus R M ≃ₐ[R] Torus R M, ∀ i,
      e (characterUnits R f i : Torus R M) = (scalarUnits f c i : Torus R M) := by
  obtain ⟨e, he⟩ := TorusTranslation.primitive_translation f hf hs
    (basisCharacter Finsupp.basisSingleOne c)
  refine ⟨e, fun i => ?_⟩
  have h := he (Finsupp.single i 1)
  have hc : basisCharacter Finsupp.basisSingleOne c
      (Multiplicative.ofAdd (Finsupp.single i 1)) = c i :=
    basisCharacter_apply Finsupp.basisSingleOne c i
  rw [hc] at h
  exact h

def scalarEquiv [Module.Finite ℤ M]
    (f : (ι →₀ ℤ) →ₗ[ℤ] M) (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) (c : ι → Rˣ) :
    LocalAlgebra (characterUnits R f) ≃ₐ[MvPolynomial ι R] LocalAlgebra (scalarUnits f c) :=
  LocalCoefficientChange.parameterEquiv
    (exists_coefficient_translation f hf hs c).choose (characterUnits R f) (scalarUnits f c)
    (exists_coefficient_translation f hf hs c).choose_spec

theorem scalarEquiv_x [Module.Finite ℤ M]
    (f : (ι →₀ ℤ) →ₗ[ℤ] M) (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) (c : ι → Rˣ) (i : ι) :
    scalarEquiv f hf hs c (x (characterUnits R f) i) = x (scalarUnits f c) i := by
  change LocalCoefficientChange.quotientEquiv
    (exists_coefficient_translation f hf hs c).choose (characterUnits R f) (scalarUnits f c)
    (exists_coefficient_translation f hf hs c).choose_spec (x (characterUnits R f) i) = _
  exact LocalCoefficientChange.quotientEquiv_x
    (exists_coefficient_translation f hf hs c).choose (characterUnits R f) (scalarUnits f c)
    (exists_coefficient_translation f hf hs c).choose_spec i

theorem scalar_parameters_smooth [Fintype ι] [Fintype β]
    (bM : Basis β ℤ M) (f : (ι →₀ ℤ) →ₗ[ℤ] M) (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) (c : ι → Rˣ) :
    Algebra.Smooth (MvPolynomial ι R) (LocalAlgebra (scalarUnits f c)) := by
  letI : Module.Finite ℤ M := Module.Finite.of_basis bM
  obtain ⟨n, s⟩ := (LinearMap.range f).smithNormalForm bM
  letI := local_character_parameters_smooth (R := R) f hf s (fun i => by
    simp only [SaturatedSmith.coefficient_natAbs s hs, Nat.cast_one, isUnit_one])
  exact Algebra.Smooth.of_equiv (scalarEquiv f hf hs c)

theorem scalar_parameters_flat [Fintype β]
    (bM : Basis β ℤ M) (f : (ι →₀ ℤ) →ₗ[ℤ] M) (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) (c : ι → Rˣ) :
    Module.Flat (MvPolynomial ι R) (LocalAlgebra (scalarUnits f c)) := by
  letI : Module.Finite ℤ M := Module.Finite.of_basis bM
  obtain ⟨n, s⟩ := (LinearMap.range f).smithNormalForm bM
  letI := ActualOpenRegular.local_character_parameters_flat (R := R) f hf s
  exact Module.Flat.of_linearEquiv (scalarEquiv f hf hs c).symm.toLinearEquiv

#print axioms scalarUnits
#print axioms exists_coefficient_translation
#print axioms scalarEquiv
#print axioms scalarEquiv_x
#print axioms scalar_parameters_smooth
#print axioms scalar_parameters_flat
end Verification.ScalarLocalExchange
