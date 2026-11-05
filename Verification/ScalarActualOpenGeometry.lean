/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarActualOpenChart
import Verification.ScalarLocalSmooth

/-!
# Scalar Actual Open Geometry

Smoothness and the simultaneous original-coordinate parameter map for
the actual global open exchange chart, transferred through the proved
base-algebra equivalence. All selected original coordinates remain present.
-/

noncomputable section
universe u
namespace Verification.ScalarActualOpenGeometry
open MvPolynomial Verification.ScalarActualOpenChart
open Verification.ActualOpenGeometry (columnMap columnMap_single)
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]

variable (a b : (ι ⊕ τ) → Rˣ)

omit [Fintype ι] in
theorem characters_eq (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) :
    ScalarActualOpenChart.characters R ι κ τ a b B = ScalarLocalSmooth.scaledCharacters (R := R) (columnMap ι κ τ B)
      (fun i => a (Sum.inl i) * (b (Sum.inl i))⁻¹) := by
  funext i
  unfold ScalarActualOpenChart.characters ScalarCharacterLocalForm.characterUnit
    ScalarLocalSmooth.scaledCharacters LocalExchangeSmooth.characterUnits
  rw [columnMap_single]
  rfl

theorem globalOpen_smooth (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0)
    (hf : Function.Injective (columnMap ι κ τ B))
    (hs : FreezingLattice.Saturated (LinearMap.range (columnMap ι κ τ B))) :
    Algebra.Smooth R (GlobalOpen R ι κ τ a b j B) := by
  letI : Algebra.Smooth R (LocalExchangeSmooth.LocalAlgebra (ScalarActualOpenChart.characters R ι κ τ a b B)) := by
    rw [characters_eq]
    exact ScalarLocalSmooth.local_smooth_saturated (columnMap ι κ τ B)
      (fun i => a (Sum.inl i) * (b (Sum.inl i))⁻¹) Finsupp.basisSingleOne hf hs
  exact Algebra.Smooth.of_equiv (globalOpenEquiv R ι κ τ a b j B hB).symm

def globalParameterMap (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) :
    MvPolynomial ι R →ₐ[R] GlobalOpen R ι κ τ a b j B := aeval (globalCoordinate R ι κ τ a b j B)

instance globalParameterAlgebra (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) :
    Algebra (MvPolynomial ι R) (GlobalOpen R ι κ τ a b j B) :=
  (globalParameterMap R ι κ τ a b j B).toRingHom.toAlgebra

theorem globalParameter_X (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (i : ι) :
    algebraMap (MvPolynomial ι R) (GlobalOpen R ι κ τ a b j B) (X i) =
      globalCoordinate R ι κ τ a b j B i := aeval_X _ _

def globalParameterEquiv (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0) :
    GlobalOpen R ι κ τ a b j B ≃ₐ[MvPolynomial ι R]
      LocalExchangeSmooth.LocalAlgebra (ScalarActualOpenChart.characters R ι κ τ a b B) :=
  AlgEquiv.ofRingEquiv (f := (globalOpenEquiv R ι κ τ a b j B hB).toRingEquiv) (fun p => by
    have h : (globalOpenEquiv R ι κ τ a b j B hB).toAlgHom.comp (globalParameterMap R ι κ τ a b j B) =
        LocalExchangeParameters.parameterMap (R := R) (ScalarActualOpenChart.characters R ι κ τ a b B) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, globalParameterMap, aeval_X,
        LocalExchangeParameters.parameterMap]
      exact globalOpenEquiv_coordinate R ι κ τ a b j B hB i
    exact AlgHom.congr_fun h p)

theorem globalOpen_parameters_smooth (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0)
    (hf : Function.Injective (columnMap ι κ τ B))
    (hs : FreezingLattice.Saturated (LinearMap.range (columnMap ι κ τ B))) :
    Algebra.Smooth (MvPolynomial ι R) (GlobalOpen R ι κ τ a b j B) := by
  letI : Algebra.Smooth (MvPolynomial ι R)
      (LocalExchangeSmooth.LocalAlgebra (ScalarActualOpenChart.characters R ι κ τ a b B)) := by
    rw [characters_eq]
    exact ScalarLocalSmooth.parameters_smooth_saturated (columnMap ι κ τ B)
      (fun i => a (Sum.inl i) * (b (Sum.inl i))⁻¹) Finsupp.basisSingleOne hf hs
  exact Algebra.Smooth.of_equiv (globalParameterEquiv R ι κ τ a b j B hB).symm

#print axioms characters_eq
#print axioms globalOpen_smooth
#print axioms globalParameterMap
#print axioms globalParameterAlgebra
#print axioms globalParameter_X
#print axioms globalParameterEquiv
#print axioms globalOpen_parameters_smooth
end Verification.ScalarActualOpenGeometry
