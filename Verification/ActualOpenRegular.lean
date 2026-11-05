/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CharacterMapFlat
import Verification.LocalParameterFlat
import Verification.PolynomialRegularSequence
import Verification.OpenZeroLayer

/-!
# Actual Open Regular

The original x-coordinates in the actual global open exchange chart
are a weakly regular sequence in every order without repetitions. This
uses actual flatness of the parameter map, proved independently of tame
smoothness. Nonemptiness of the zero layer gives a regular sequence.
-/
noncomputable section
universe u
namespace Verification.ActualOpenRegular
open MvPolynomial Verification.ActualOpenChart Verification.ActualOpenGeometry
open Verification.LocalExchangeSmooth RingTheory.Sequence
variable {R M α ι : Type u} [CommRing R] [AddCommGroup M]

theorem local_character_parameters_flat
    (f : (ι →₀ ℤ) →ₗ[ℤ] M) (hf : Function.Injective f)
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) α n) :
    Module.Flat (MvPolynomial ι R) (LocalAlgebra (characterUnits R f)) := by
  letI := (CharacterMapSmooth.characterMap (R := R) f).toRingHom.toAlgebra
  letI := CharacterMapFlat.characterMap_flat (R := R) f hf Finsupp.basisSingleOne s
  apply LocalParameterFlat.parameter_flat (characterUnits R f)
  intro i
  exact CharacterMapSmooth.characterMap_monomial f (Finsupp.single i 1)

variable (R ι) (κ τ : Type u) [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0)
variable (hf : Function.Injective (columnMap ι κ τ B))

include hB hf in
theorem globalOpen_parameters_flat : Module.Flat (MvPolynomial ι R) (GlobalOpen R ι κ τ j B) := by
  obtain ⟨n,s⟩ := (LinearMap.range (columnMap ι κ τ B)).smithNormalForm Finsupp.basisSingleOne
  letI : Module.Flat (MvPolynomial ι R)
      (LocalAlgebra (ActualOpenChart.characters R ι κ τ B)) := by
    rw [characters_eq]
    exact local_character_parameters_flat (columnMap ι κ τ B) hf s
  exact Module.Flat.of_linearEquiv (globalParameterEquiv R ι κ τ j B hB).toLinearEquiv

include hB hf in
theorem original_coordinates_weaklyRegular (l : List ι) (hl : l.Nodup) :
    IsWeaklyRegular (GlobalOpen R ι κ τ j B) (l.map (globalCoordinate R ι κ τ j B)) := by
  letI := globalOpen_parameters_flat R ι κ τ j B hB hf
  simpa only [globalParameter_X] using
    PolynomialRegularSequence.flat_variables_weaklyRegular R ι (GlobalOpen R ι κ τ j B) l hl

theorem coordinate_list_le_zeroIdeal (l : List ι) :
    Ideal.ofList (l.map (globalCoordinate R ι κ τ j B)) ≤ ActualOpenConormal.zeroIdeal R ι κ τ j B := by
  apply Ideal.span_le.mpr
  intro p hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  exact Ideal.subset_span (Set.mem_range_self i)

include hB hf in
theorem original_coordinates_regular [Nontrivial (ActualOpenConormal.ZeroLayer R ι κ τ j B)]
    (l : List ι) (hl : l.Nodup) :
    IsRegular (GlobalOpen R ι κ τ j B) (l.map (globalCoordinate R ι κ τ j B)) := by
  have hproper : ActualOpenConormal.zeroIdeal R ι κ τ j B ≠ ⊤ :=
    Ideal.Quotient.zero_ne_one_iff.mp (zero_ne_one : (0 : ActualOpenConormal.ZeroLayer R ι κ τ j B) ≠ 1)
  have hlproper : Ideal.ofList (l.map (globalCoordinate R ι κ τ j B)) ≠ ⊤ := by
    intro ht
    exact hproper (top_unique (ht ▸ coordinate_list_le_zeroIdeal R ι κ τ j B l))
  refine ⟨original_coordinates_weaklyRegular R ι κ τ j B hB hf l hl, ?_⟩
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hlproper.symm

include hB hf in
theorem original_coordinates_regular_of_stratum
    [Nontrivial (ActualStratum.GlobalZeroStratum R ι κ τ j B)]
    (l : List ι) (hl : l.Nodup) :
    IsRegular (GlobalOpen R ι κ τ j B) (l.map (globalCoordinate R ι κ τ j B)) := by
  letI : Nontrivial (ActualOpenConormal.ZeroLayer R ι κ τ j B) :=
    (OpenZeroLayer.stratumEquiv R ι κ τ j B).surjective.nontrivial
  exact original_coordinates_regular R ι κ τ j B hB hf l hl

#print axioms local_character_parameters_flat
#print axioms globalOpen_parameters_flat
#print axioms original_coordinates_weaklyRegular
#print axioms coordinate_list_le_zeroIdeal
#print axioms original_coordinates_regular
#print axioms original_coordinates_regular_of_stratum
end Verification.ActualOpenRegular
