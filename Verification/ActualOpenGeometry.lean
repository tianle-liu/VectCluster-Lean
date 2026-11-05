/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualOpenChart

/-!
# Actual Open Geometry

Smoothness and the simultaneous original-coordinate parameter map for
the actual global open exchange chart, transferred through the proved
base-algebra equivalence. All selected original coordinates remain present.
-/

noncomputable section
universe u
namespace Verification.ActualOpenGeometry
open MvPolynomial Verification.ActualOpenChart
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]

def columnMap (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ) :=
  Finsupp.linearCombination ℤ (ActualOpenChart.column ι κ τ B)

omit [Fintype ι] in
theorem columnMap_single (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (i : ι) :
    columnMap ι κ τ B (Finsupp.single i 1) = ActualOpenChart.column ι κ τ B i := by
  simp [columnMap]

omit [Fintype ι] in
theorem characters_eq (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) :
    ActualOpenChart.characters R ι κ τ B = LocalExchangeSmooth.characterUnits R (columnMap ι κ τ B) := by
  funext i
  unfold ActualOpenChart.characters LocalExchangeSmooth.characterUnits
  rw [columnMap_single]

theorem globalOpen_smooth (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0)
    (hf : Function.Injective (columnMap ι κ τ B))
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range (columnMap ι κ τ B)) κ n)
    (he : ∀ i, IsUnit ((s.a i).natAbs : R)) :
    Algebra.Smooth R (GlobalOpen R ι κ τ j B) := by
  letI : Algebra.Smooth R (LocalExchangeSmooth.LocalAlgebra (ActualOpenChart.characters R ι κ τ B)) := by
    rw [characters_eq]
    exact LocalExchangeSmooth.local_character_smooth (columnMap ι κ τ B) hf s he
  exact Algebra.Smooth.of_equiv (globalOpenEquiv R ι κ τ j B hB).symm

def globalParameterMap (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) :
    MvPolynomial ι R →ₐ[R] GlobalOpen R ι κ τ j B := aeval (globalCoordinate R ι κ τ j B)

instance globalParameterAlgebra (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) :
    Algebra (MvPolynomial ι R) (GlobalOpen R ι κ τ j B) :=
  (globalParameterMap R ι κ τ j B).toRingHom.toAlgebra

theorem globalParameter_X (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (i : ι) :
    algebraMap (MvPolynomial ι R) (GlobalOpen R ι κ τ j B) (X i) =
      globalCoordinate R ι κ τ j B i := aeval_X _ _

def globalParameterEquiv (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0) :
    GlobalOpen R ι κ τ j B ≃ₐ[MvPolynomial ι R]
      LocalExchangeSmooth.LocalAlgebra (ActualOpenChart.characters R ι κ τ B) :=
  AlgEquiv.ofRingEquiv (f := (globalOpenEquiv R ι κ τ j B hB).toRingEquiv) (fun p => by
    have h : (globalOpenEquiv R ι κ τ j B hB).toAlgHom.comp (globalParameterMap R ι κ τ j B) =
        LocalExchangeParameters.parameterMap (R := R) (ActualOpenChart.characters R ι κ τ B) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, globalParameterMap, aeval_X,
        LocalExchangeParameters.parameterMap]
      exact globalOpenEquiv_coordinate R ι κ τ j B hB i
    exact AlgHom.congr_fun h p)

theorem globalOpen_parameters_smooth (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0)
    (hf : Function.Injective (columnMap ι κ τ B))
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range (columnMap ι κ τ B)) κ n)
    (he : ∀ i, IsUnit ((s.a i).natAbs : R)) :
    Algebra.Smooth (MvPolynomial ι R) (GlobalOpen R ι κ τ j B) := by
  letI : Algebra.Smooth (MvPolynomial ι R)
      (LocalExchangeSmooth.LocalAlgebra (ActualOpenChart.characters R ι κ τ B)) := by
    rw [characters_eq]
    exact LocalExchangeParameters.local_character_parameters_smooth (columnMap ι κ τ B) hf s he
  exact Algebra.Smooth.of_equiv (globalParameterEquiv R ι κ τ j B hB).symm

theorem globalOpen_smooth_charZero {k : Type u} [Field k] [CharZero k]
    (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0)
    (hf : Function.Injective (columnMap ι κ τ B)) :
    Algebra.Smooth k (GlobalOpen k ι κ τ j B) := by
  obtain ⟨n,s⟩ := (LinearMap.range (columnMap ι κ τ B)).smithNormalForm Finsupp.basisSingleOne
  apply globalOpen_smooth k ι κ τ j B hB hf s
  intro i
  exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr
    (Int.natAbs_ne_zero.mpr (SmithCharacters.smith_coefficient_ne_zero s i)))

theorem globalOpen_parameters_smooth_charZero {k : Type u} [Field k] [CharZero k]
    (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0)
    (hf : Function.Injective (columnMap ι κ τ B)) :
    Algebra.Smooth (MvPolynomial ι k) (GlobalOpen k ι κ τ j B) := by
  obtain ⟨n,s⟩ := (LinearMap.range (columnMap ι κ τ B)).smithNormalForm Finsupp.basisSingleOne
  apply globalOpen_parameters_smooth k ι κ τ j B hB hf s
  intro i
  exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr
    (Int.natAbs_ne_zero.mpr (SmithCharacters.smith_coefficient_ne_zero s i)))

#print axioms columnMap
#print axioms columnMap_single
#print axioms characters_eq
#print axioms globalOpen_smooth
#print axioms globalParameterMap
#print axioms globalParameterAlgebra
#print axioms globalParameter_X
#print axioms globalParameterEquiv
#print axioms globalOpen_parameters_smooth
#print axioms globalOpen_smooth_charZero
#print axioms globalOpen_parameters_smooth_charZero
end Verification.ActualOpenGeometry
