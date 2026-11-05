/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalMatrixSplittings

/-!
# Path Original AS

AS for every actual independent stratum of Y of even length and Z of
arbitrary length, from the constructed integral matrix splittings.
-/
noncomputable section
namespace Verification.PathOriginalAS
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover Verification.IndependentChartIndex
open Verification.PathOriginalMatrixSplittings

theorem of_split {κ : Type} [Fintype κ] (n : ℕ)
    (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
    (hB : ∀ a i,B (Sum.inl a) (Sum.inl i)=PathLattice.pathMatrix n a i)
    (r : ((Fin n ⊕ κ) → ℤ) →ₗ[ℤ] (Fin n → ℤ))
    (hr : r.comp (Matrix.mulVecLin (fun a i=>B a (Sum.inl i)))=LinearMap.id)
    (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I) :
    Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I) ∧
      FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)) := by
  apply (GlobalSelectedColumns.AS_iff κ n B I).mpr
  apply FullMatrixSelectedSplit.AS _ I r hr
  intro i hi j hj
  exact independent_principal_zero κ n I B
    (PathOriginalIndependence.positive_order B hB)
    (PathOriginalIndependence.negative_order B hB)
    (PathOriginalIndependence.support B hB) hI i j hi hj

theorem y (m : ℕ) (I : Finset (Fin (2*m)))
    (hI : Independent (laterWeights Empty (2*m) (PathOriginalYPresentation.matrix (2*m))) I) :
    Function.Injective (GlobalExchangeSmooth.selectedMap Empty (2*m) (PathOriginalYPresentation.matrix (2*m)) I) ∧
      FreezingLattice.Saturated (LinearMap.range
        (GlobalExchangeSmooth.selectedMap Empty (2*m) (PathOriginalYPresentation.matrix (2*m)) I)) :=
  of_split (2*m) (PathOriginalYPresentation.matrix (2*m)) (fun _ _=>rfl)
    (evenRetraction m) (even_left m _ (fun _ _=>rfl)) I hI

theorem z_even (m : ℕ) (I : Finset (Fin (2*m)))
    (hI : Independent (laterWeights (Fin 1) (2*m) (PathOriginalZPresentation.matrix (2*m))) I) :
    Function.Injective (GlobalExchangeSmooth.selectedMap (Fin 1) (2*m) (PathOriginalZPresentation.matrix (2*m)) I) ∧
      FreezingLattice.Saturated (LinearMap.range
        (GlobalExchangeSmooth.selectedMap (Fin 1) (2*m) (PathOriginalZPresentation.matrix (2*m)) I)) :=
  of_split (2*m) (PathOriginalZPresentation.matrix (2*m)) (fun _ _=>rfl)
    (evenRetraction m) (even_left m _ (fun _ _=>rfl)) I hI

theorem z_odd (m : ℕ) (I : Finset (Fin (2*m+1)))
    (hI : Independent (laterWeights (Fin 1) (2*m+1) (PathOriginalZPresentation.matrix (2*m+1))) I) :
    Function.Injective (GlobalExchangeSmooth.selectedMap (Fin 1) (2*m+1) (PathOriginalZPresentation.matrix (2*m+1)) I) ∧
      FreezingLattice.Saturated (LinearMap.range
        (GlobalExchangeSmooth.selectedMap (Fin 1) (2*m+1) (PathOriginalZPresentation.matrix (2*m+1)) I)) :=
  of_split (2*m+1) (PathOriginalZPresentation.matrix (2*m+1)) (fun _ _=>rfl)
    (oddZRetraction m) (odd_z_left m) I hI

theorem z (n : ℕ) (I : Finset (Fin n))
    (hI : Independent (laterWeights (Fin 1) n (PathOriginalZPresentation.matrix n)) I) :
    Function.Injective (GlobalExchangeSmooth.selectedMap (Fin 1) n (PathOriginalZPresentation.matrix n) I) ∧
      FreezingLattice.Saturated (LinearMap.range
        (GlobalExchangeSmooth.selectedMap (Fin 1) n (PathOriginalZPresentation.matrix n) I)) := by
  have hn : ∃ m,n=2*m ∨ n=2*m+1 := ⟨n/2,by omega⟩
  obtain ⟨m,hm|hm⟩ := hn
  · subst n;exact z_even m I hI
  · subst n;exact z_odd m I hI

#print axioms of_split
#print axioms y
#print axioms z_even
#print axioms z_odd
#print axioms z
end Verification.PathOriginalAS
