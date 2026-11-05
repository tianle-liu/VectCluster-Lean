/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualCliqueColumns
import Verification.GlobalSelectedColumns
import Verification.OriginalScalarOne

/-!
# Sevenfold Exchange Matrix

The literal extended exchange matrix of the paper's sevenfold.
Vertices 1,...,5 are Fin 5 indices 0,...,4; the frozen clique colors are
{1,2,5} and {3,4}. Saturation is proved from their actual frozen rows.
-/
namespace Verification.SevenfoldExchangeMatrix
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentChartIndex

def principal : Matrix (Fin 5) (Fin 5) ℤ :=
  ![![0,2,0,0,2], ![-2,0,0,0,2], ![0,0,0,2,2],
    ![0,0,-2,0,2], ![-2,-2,-2,-2,0]]

def color : Fin 5 → Fin 2 := ![0,0,1,1,0]

def matrix : (Fin 5 ⊕ Fin 2) → (Fin 5 ⊕ Empty) → ℤ :=
  fun a => Sum.elim (fun i => Sum.elim (fun j => principal j i)
    (fun c => if color i = c then 1 else 0) a) Empty.elim

theorem mutable_entry (a i : Fin 5) : matrix (Sum.inl a) (Sum.inl i) = principal a i := rfl

theorem frozen_entry (c : Fin 2) (i : Fin 5) :
    matrix (Sum.inr c) (Sum.inl i) = if color i = c then 1 else 0 := rfl

theorem positive_order : ∀ a i : Fin 5, ¬a < i → (matrix (Sum.inl a) (Sum.inl i)).toNat = 0 := by decide

theorem negative_order : ∀ a i : Fin 5, ¬i < a → (-matrix (Sum.inl a) (Sum.inl i)).toNat = 0 := by decide

theorem support : ∀ i j, earlierWeights (Fin 2) 5 matrix i j = 0 ↔ laterWeights (Fin 2) 5 matrix i j = 0 := by decide

theorem same_color_nonzero : ∀ a i : Fin 5, a ≠ i → color a = color i → principal a i ≠ 0 := by decide

theorem independent_colors (I : Finset (Fin 5)) (hI : Independent (laterWeights (Fin 2) 5 matrix) I) :
    Function.Injective (fun i : Selected 5 I => color i.val) := by
  intro a i hai
  apply Subtype.ext
  by_contra hne
  exact same_color_nonzero a.val i.val hne hai
    (independent_principal_zero (Fin 2) 5 I matrix positive_order negative_order support hI a.val i.val a.property i.property)

theorem selected_AS (I : Finset (Fin 5)) (hI : Independent (laterWeights (Fin 2) 5 matrix) I) :
    Function.Injective (Verification.GlobalExchangeSmooth.selectedMap (Fin 2) 5 matrix I) ∧
      Verification.FreezingLattice.Saturated
        (LinearMap.range (Verification.GlobalExchangeSmooth.selectedMap (Fin 2) 5 matrix I)) := by
  classical
  exact Verification.ActualCliqueColumns.actual_clique_AS
    (Verification.IndependentChartIndex.matrix (Fin 2) 5 I matrix)
    (fun i : Selected 5 I => color i.val) (independent_colors I hI) (fun _ _ => rfl)

theorem anticlique_AS (I : Finset (Fin 5)) (hI : Independent (laterWeights (Fin 2) 5 matrix) I) :
    Verification.AnticliqueSubcolumns.AS (fun a i => matrix a (Sum.inl i)) I :=
  (Verification.GlobalSelectedColumns.AS_iff (Fin 2) 5 matrix I).mp (selected_AS I hI)

variable (R : Type) [CommRing R]

abbrev Ring := Global R (Fin 2) 5 matrix

theorem smooth : Algebra.Smooth R (Ring R) :=
  Verification.GlobalExchangeSmooth.global_smooth_saturated R (Fin 2) 5 matrix
    positive_order negative_order support (fun I hI => (selected_AS I hI).1)
    (fun I hI => (selected_AS I hI).2)

theorem domain [IsDomain R] : IsDomain (Ring R) :=
  Verification.OriginalScalarOne.global_domain R (Fin 2) 5 matrix
    positive_order negative_order support anticlique_AS

#print axioms principal
#print axioms color
#print axioms matrix
#print axioms mutable_entry
#print axioms frozen_entry
#print axioms positive_order
#print axioms negative_order
#print axioms support
#print axioms same_color_nonzero
#print axioms independent_colors
#print axioms selected_AS
#print axioms anticlique_AS
#print axioms Ring
#print axioms smooth
#print axioms domain
end Verification.SevenfoldExchangeMatrix
