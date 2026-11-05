/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IndependentBasicOpen
import Verification.SaturatedSmith

/-!
# Global Exchange Smooth

Smoothness of the fixed frozen exchange presentation. The hypotheses
are imposed on the actual columns selected by each independent set, after
deleting its zero rows. No injectivity of the whole exchange matrix is used.
The characteristic-zero rank case and the saturated case follow directly.
-/
noncomputable section
namespace Verification.GlobalExchangeSmooth
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.ActualOpenGeometry
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

def selectedMap (I : Finset (Fin n)) : (Selected n I →₀ ℤ) →ₗ[ℤ] ((Other n I ⊕ κ) →₀ ℤ) :=
  columnMap (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B)

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)

include hpos hneg hsupport

theorem basicOpen_smooth (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I)
    (hf : Function.Injective (selectedMap κ n B I)) {m : ℕ}
    (s : Basis.SmithNormalForm (LinearMap.range (selectedMap κ n B I)) (Other n I ⊕ κ) m)
    (he : ∀ i, IsUnit ((s.a i).natAbs : R)) :
    Algebra.Smooth R (IndependentBasicOpen.BasicOpen R κ n I B) := by
  letI : Algebra.Smooth R (ActualOpenChart.GlobalOpen R (Selected n I) (Other n I ⊕ κ)
      (Other n I) Sum.inl (matrix κ n I B)) :=
    globalOpen_smooth R (Selected n I) (Other n I ⊕ κ) (Other n I) Sum.inl
      (matrix κ n I B) (matrix_zero_block κ n I B hpos hneg hsupport hI) hf s he
  exact Algebra.Smooth.of_equiv (IndependentBasicOpen.chartEquiv R κ n I B).symm

theorem global_smooth_tame
    (hf : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
      Function.Injective (selectedMap κ n B I))
    (htame : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
      ∃ (m : ℕ) (s : Basis.SmithNormalForm (LinearMap.range (selectedMap κ n B I))
        (Other n I ⊕ κ) m), ∀ i, IsUnit ((s.a i).natAbs : R)) :
    Algebra.Smooth R (Global R κ n B) := by
  apply FrozenGlobalSmooth.global_smooth_of_charts R κ n B hpos hneg hsupport
  intro I
  obtain ⟨m, s, he⟩ := htame I.1 I.2
  exact basicOpen_smooth R κ n B hpos hneg hsupport I.1 I.2 (hf I.1 I.2) s he

theorem global_smooth_saturated
    (hf : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
      Function.Injective (selectedMap κ n B I))
    (hs : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
      FreezingLattice.Saturated (LinearMap.range (selectedMap κ n B I))) :
    Algebra.Smooth R (Global R κ n B) := by
  apply global_smooth_tame R κ n B hpos hneg hsupport hf
  intro I hI
  obtain ⟨m,s⟩ := (LinearMap.range (selectedMap κ n B I)).smithNormalForm Finsupp.basisSingleOne
  refine ⟨m,s,fun i => ?_⟩
  simp only [SaturatedSmith.coefficient_natAbs s (hs I hI), Nat.cast_one, isUnit_one]

theorem global_smooth_charZero (k : Type) [Field k] [CharZero k]
    (hf : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
      Function.Injective (selectedMap κ n B I)) :
    Algebra.Smooth k (Global k κ n B) := by
  apply global_smooth_tame k κ n B hpos hneg hsupport hf
  intro I _
  obtain ⟨m,s⟩ := (LinearMap.range (selectedMap κ n B I)).smithNormalForm Finsupp.basisSingleOne
  refine ⟨m,s,fun i => ?_⟩
  exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr
    (Int.natAbs_ne_zero.mpr (SmithCharacters.smith_coefficient_ne_zero s i)))

#print axioms selectedMap
#print axioms basicOpen_smooth
#print axioms global_smooth_tame
#print axioms global_smooth_saturated
#print axioms global_smooth_charZero
end Verification.GlobalExchangeSmooth
