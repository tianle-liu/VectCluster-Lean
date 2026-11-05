/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmoothParameterQuotient
import Verification.ActualTransverseRegular
import Verification.SaturatedSmith

/-!
# Actual Transverse Smooth

The actual intermediate closed chart used for the transverse slice
is smooth over the coefficient ring. Its equations set exactly the old
selected parameters to zero; parameter smoothness supplies the lifts.
-/
noncomputable section
universe u
namespace Verification.ActualTransverseSmooth
open Verification.ActualOpenChart Verification.ActualOpenGeometry
open Verification.ActualTransverseSlice
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (v : ι)

theorem intermediate_smooth [Algebra.Smooth (MvPolynomial ι R) (GlobalOpen R ι κ τ j B)] :
    Algebra.Smooth R (Intermediate R ι κ τ j B v) := by
  letI : IsScalarTower R (MvPolynomial ι R) (GlobalOpen R ι κ τ j B) :=
    IsScalarTower.of_algHom (globalParameterMap R ι κ τ j B)
  have hi : SmoothParameterQuotient.ideal R (GlobalOpen R ι κ τ j B) ι {i | i ≠ v} =
      partialIdeal R ι κ τ j B v := by
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    exact globalParameter_X R ι κ τ j B i.val
  change Algebra.Smooth R (GlobalOpen R ι κ τ j B ⧸ partialIdeal R ι κ τ j B v)
  rw [← hi]
  exact SmoothParameterQuotient.smooth R (GlobalOpen R ι κ τ j B) ι {i | i ≠ v}

theorem intermediate_smooth_AS
    (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0)
    (hf : Function.Injective (columnMap ι κ τ B))
    (hs : FreezingLattice.Saturated (LinearMap.range (columnMap ι κ τ B))) :
    Algebra.Smooth R (Intermediate R ι κ τ j B v) := by
  letI := SaturatedSmith.globalOpen_parameters_smooth_saturated R ι κ τ j B hB hf hs
  exact intermediate_smooth R ι κ τ j B v

theorem intermediate_smooth_tame
    (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0)
    (hf : Function.Injective (columnMap ι κ τ B))
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range (columnMap ι κ τ B)) κ n)
    (he : ∀ i, IsUnit ((s.a i).natAbs : R)) :
    Algebra.Smooth R (Intermediate R ι κ τ j B v) := by
  letI := globalOpen_parameters_smooth R ι κ τ j B hB hf s he
  exact intermediate_smooth R ι κ τ j B v

#print axioms intermediate_smooth
#print axioms intermediate_smooth_AS
#print axioms intermediate_smooth_tame
end Verification.ActualTransverseSmooth
