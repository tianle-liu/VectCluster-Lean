/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalEdgelessGeometry
import Verification.UniversalExchangeTransport

/-!
# Original Edgeless Standard

The original edgeless exchange algebra has the literal standard model
R[t_1^{±1},...,t_{m-n}^{±1}][x_1,...,x_n,y_1,...,y_n,
(x_1*y_1-1)^{-1},...,(x_n*y_n-1)^{-1}].
All identifications, including the number of complementary torus factors,
are derived from AS; the original x coordinates are fixed.
-/
noncomputable section
namespace Verification.OriginalEdgelessStandard
open Verification.OriginalEdgelessGeometry Verification.FrozenAcyclicCover
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hAS : AnticliqueSubcolumns.AS (fun a i => B a (Sum.inl i)) Finset.univ)

def complementCoordinates : Complement κ n B ≃ₗ[ℤ] (Fin (Fintype.card κ - n) →₀ ℤ) :=
  (PrimitiveTorusRank.quotientCoordinates (columns κ n B)
    ((GlobalSelectedColumns.AS_iff κ n B Finset.univ).mpr hAS).2).trans
    (Finsupp.domLCongr (finCongr (complement_dimension κ n B hAS)))

def complementTorus : CharacterMapSmooth.Torus R (Complement κ n B) ≃ₐ[R]
    OriginalTorus.Torus R (Fin (Fintype.card κ - n)) :=
  MonoidAlgebra.domCongr R R
    (complementCoordinates κ n B hAS).toAddEquiv.toMultiplicative

abbrev StandardModel := UniversalExchangeChart.OpenPolynomial
  (OriginalTorus.Torus R (Fin (Fintype.card κ - n))) (Fin n)

variable (hzero : ∀ a i : Fin n, B (Sum.inl a) (Sum.inl i) = 0)

def standardEquiv : Global R κ n B ≃ₐ[R] StandardModel R κ n :=
  (coordinates R κ n B hzero hAS).trans
    (UniversalExchangeTransport.openEquiv (complementTorus R κ n B hAS) (verticesEquiv n))

theorem standardEquiv_x (i : Fin n) :
    standardEquiv R κ n B hAS hzero (initial R κ n B (Sum.inl i)) =
      algebraMap
        (UniversalExchangeChart.Polynomial (OriginalTorus.Torus R (Fin (Fintype.card κ - n))) (Fin n))
        (StandardModel R κ n) (MvPolynomial.X (Sum.inl i)) := by
  change UniversalExchangeTransport.openEquiv (complementTorus R κ n B hAS) (verticesEquiv n)
    (coordinates R κ n B hzero hAS (initial R κ n B (Sum.inl i))) = _
  rw [coordinates_x R κ n B hzero hAS (⟨i, Finset.mem_univ i⟩ : Vertices n),
    UniversalExchangeTransport.openEquiv_x]
  rfl

#print axioms complementCoordinates
#print axioms complementTorus
#print axioms StandardModel
#print axioms standardEquiv
#print axioms standardEquiv_x
end Verification.OriginalEdgelessStandard
