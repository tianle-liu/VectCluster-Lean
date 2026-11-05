/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualOpenSplit
import Verification.IndependentOpenCoordinates
import Verification.GlobalSelectedColumns
import Verification.PrimitiveTorusRank

/-!
# Original Edgeless Geometry

For an actual exchange matrix with zero mutable block, the all-vertex
chart is the entire original ring. AS constructs its isomorphism to the
polynomial algebra with every x_i*y_i-1 inverted over a complementary torus.
The complement has rank |frozen|-|mutable|; no coordinate identification or
cohomological vanishing is assumed. This is the geometry in the edgeless
case of manuscript.tex.
-/
noncomputable section
namespace Verification.OriginalEdgelessGeometry
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.CharacterMapSmooth
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

abbrev Vertices := Selected n Finset.univ
abbrev Rows := Other n Finset.univ ⊕ κ
abbrev columns := GlobalExchangeSmooth.selectedMap κ n B Finset.univ
abbrev Complement := (Rows κ n →₀ ℤ) ⧸ LinearMap.range (columns κ n B)

def verticesEquiv : Vertices n ≃ Fin n where
  toFun := Subtype.val
  invFun i := ⟨i, Finset.mem_univ i⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rowsEquiv : Rows κ n ≃ κ where
  toFun a := match a with
    | Sum.inl i => False.elim (i.property (Finset.mem_univ i.val))
    | Sum.inr k => k
  invFun := Sum.inr
  left_inv a := by
    cases a with
    | inl i => exact False.elim (i.property (Finset.mem_univ i.val))
    | inr k => rfl
  right_inv _ := rfl

theorem chartValue_one : IndependentBasicOpen.chartValue R κ n Finset.univ B = 1 := by
  classical
  simp [IndependentBasicOpen.chartValue, chartElement]

def wholeChart : Global R κ n B ≃ₐ[R]
    IndependentBasicOpen.BasicOpen R κ n Finset.univ B :=
  (IsLocalization.atUnit (Global R κ n B)
    (IndependentBasicOpen.BasicOpen R κ n Finset.univ B)
    (IndependentBasicOpen.chartValue R κ n Finset.univ B)
    ((chartValue_one R κ n B).symm ▸ isUnit_one)).restrictScalars R

theorem wholeChart_coordinate (i : Vertices n) :
    wholeChart R κ n B (initial R κ n B (Sum.inl i.val)) =
      IndependentOpenCoordinates.selectedCoordinate R κ n Finset.univ B i := rfl

variable (hzero : ∀ a i : Fin n, B (Sum.inl a) (Sum.inl i) = 0)
variable (hAS : AnticliqueSubcolumns.AS (fun a i => B a (Sum.inl i)) Finset.univ)

include hzero in
omit [Fintype κ] in
theorem independent : Independent (laterWeights κ n B) Finset.univ := by
  intro i _ j _
  simp [Verification.ExchangeRing.Adjacent, laterWeights, hzero]

include hAS in
theorem complement_rank : Module.finrank ℤ (Complement κ n B) + n = Fintype.card κ := by
  have hs := (GlobalSelectedColumns.AS_iff κ n B Finset.univ).mpr hAS
  have hr := PrimitiveTorusRank.quotient_rank (columns κ n B)
    (Finsupp.basisSingleOne : Basis (Vertices n) ℤ (Vertices n →₀ ℤ)) hs.1 hs.2
  simpa only [Fintype.card_congr (verticesEquiv n), Fintype.card_congr (rowsEquiv κ n),
    Fintype.card_fin] using hr

include hAS in
theorem enough_frozen : n ≤ Fintype.card κ := by
  have := complement_rank κ n B hAS
  omega

include hAS in
theorem complement_dimension : Module.finrank ℤ (Complement κ n B) = Fintype.card κ - n := by
  have := complement_rank κ n B hAS
  omega

def coordinates : Global R κ n B ≃ₐ[R]
    UniversalExchangeChart.OpenPolynomial (Torus R (Complement κ n B)) (Vertices n) :=
  ((wholeChart R κ n B).trans
    (IndependentBasicOpen.chartEquiv R κ n Finset.univ B)).trans
    (ActualOpenSplit.coordinates R (Vertices n) (Rows κ n) (Other n Finset.univ)
      Sum.inl (matrix κ n Finset.univ B) (fun a i => hzero a.val i.val)
      ((GlobalSelectedColumns.AS_iff κ n B Finset.univ).mpr hAS).1
      ((GlobalSelectedColumns.AS_iff κ n B Finset.univ).mpr hAS).2)

theorem coordinates_x (i : Vertices n) :
    coordinates R κ n B hzero hAS (initial R κ n B (Sum.inl i.val)) =
      algebraMap
        (UniversalExchangeChart.Polynomial (Torus R (Complement κ n B)) (Vertices n))
        (UniversalExchangeChart.OpenPolynomial (Torus R (Complement κ n B)) (Vertices n))
          (MvPolynomial.X (Sum.inl i)) := by
  simp only [coordinates, AlgEquiv.trans_apply, wholeChart_coordinate,
    IndependentOpenCoordinates.chartEquiv_selectedCoordinate]
  exact ActualOpenSplit.coordinates_x _ _ _ _ _ _ _ _ _ i

#print axioms Vertices
#print axioms Rows
#print axioms columns
#print axioms Complement
#print axioms verticesEquiv
#print axioms rowsEquiv
#print axioms chartValue_one
#print axioms wholeChart
#print axioms wholeChart_coordinate
#print axioms independent
#print axioms complement_rank
#print axioms enough_frozen
#print axioms complement_dimension
#print axioms coordinates
#print axioms coordinates_x
end Verification.OriginalEdgelessGeometry
