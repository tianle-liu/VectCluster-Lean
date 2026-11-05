/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarActualOpenGeometry
import Verification.SmoothConormal
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Scalar Actual Open Conormal

The actual zero-coordinate ideal in an actual global open exchange chart
has the classes of the original coordinates as a conormal basis. The dual
basis supplies its algebraic normal framing. This does not assert a regular
sequence theorem or a sheaf/Gysin comparison.
-/
noncomputable section
universe u
namespace Verification.ScalarActualOpenConormal
open MvPolynomial Verification.ScalarActualOpenChart Verification.ScalarActualOpenGeometry
open Verification.ActualOpenGeometry (columnMap)
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (a b : (ι ⊕ τ) → Rˣ) (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)

def zeroIdeal : Ideal (GlobalOpen R ι κ τ a b j B) :=
  ConormalFrame.ideal (globalCoordinate R ι κ τ a b j B)

def ZeroLayer := GlobalOpen R ι κ τ a b j B ⧸ zeroIdeal R ι κ τ a b j B

instance zeroLayerCommRing : CommRing (ZeroLayer R ι κ τ a b j B) :=
  inferInstanceAs (CommRing (GlobalOpen R ι κ τ a b j B ⧸ zeroIdeal R ι κ τ a b j B))

instance conormalModule : Module (ZeroLayer R ι κ τ a b j B) (zeroIdeal R ι κ τ a b j B).Cotangent :=
  Ideal.cotangentModule _

def coordinateClass (i : ι) : (zeroIdeal R ι κ τ a b j B).Cotangent :=
  ConormalFrame.frame (globalCoordinate R ι κ τ a b j B) i

variable (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0)
variable (hf : Function.Injective (columnMap ι κ τ B))
variable (hs : FreezingLattice.Saturated (LinearMap.range (columnMap ι κ τ B)))

include hB hf hs in
theorem exists_directions :
    ∃ f : GlobalOpen R ι κ τ a b j B →+*
        TrivSqZeroExt (ZeroLayer R ι κ τ a b j B) (ι →₀ ZeroLayer R ι κ τ a b j B),
      (∀ z, (f z).fst = Ideal.Quotient.mk (zeroIdeal R ι κ τ a b j B) z) ∧
      ∀ i, f (globalCoordinate R ι κ τ a b j B i) = TrivSqZeroExt.inr (Finsupp.single i 1) := by
  letI : Algebra.Smooth (MvPolynomial ι R) (GlobalOpen R ι κ τ a b j B) :=
    globalOpen_parameters_smooth R ι κ τ a b j B hB hf hs
  letI : IsScalarTower R (MvPolynomial ι R) (GlobalOpen R ι κ τ a b j B) :=
    IsScalarTower.of_algHom (globalParameterMap R ι κ τ a b j B)
  exact SmoothConormal.exists_directions_for R (GlobalOpen R ι κ τ a b j B) ι
    (globalCoordinate R ι κ τ a b j B) (globalParameter_X R ι κ τ a b j B)

def conormalBasis : Basis ι (ZeroLayer R ι κ τ a b j B) (zeroIdeal R ι κ τ a b j B).Cotangent :=
  ConormalFrame.basis (globalCoordinate R ι κ τ a b j B)
    (exists_directions R ι κ τ a b j B hB hf hs).choose
    (exists_directions R ι κ τ a b j B hB hf hs).choose_spec.1
    (exists_directions R ι κ τ a b j B hB hf hs).choose_spec.2

theorem conormalBasis_apply (i : ι) :
    conormalBasis R ι κ τ a b j B hB hf hs i = coordinateClass R ι κ τ a b j B i :=
  ConormalFrame.basis_apply _ _ _ _ i

def conormalEquiv : (zeroIdeal R ι κ τ a b j B).Cotangent ≃ₗ[ZeroLayer R ι κ τ a b j B]
    (ι →₀ ZeroLayer R ι κ τ a b j B) := (conormalBasis R ι κ τ a b j B hB hf hs).repr

def normalBasis [DecidableEq ι] : Basis ι (ZeroLayer R ι κ τ a b j B)
    (Module.Dual (ZeroLayer R ι κ τ a b j B) (zeroIdeal R ι κ τ a b j B).Cotangent) :=
  (conormalBasis R ι κ τ a b j B hB hf hs).dualBasis

theorem normalBasis_coordinateClass [DecidableEq ι] (i l : ι) :
    normalBasis R ι κ τ a b j B hB hf hs i (coordinateClass R ι κ τ a b j B l) =
      if i = l then 1 else 0 := by
  rw [← conormalBasis_apply R ι κ τ a b j B hB hf hs l]
  dsimp only [normalBasis]
  rw [Basis.dualBasis_apply_self]
  simp only [eq_comm]

#print axioms zeroIdeal
#print axioms ZeroLayer
#print axioms zeroLayerCommRing
#print axioms conormalModule
#print axioms coordinateClass
#print axioms exists_directions
#print axioms conormalBasis
#print axioms conormalBasis_apply
#print axioms conormalEquiv
#print axioms normalBasis
#print axioms normalBasis_coordinateClass
end Verification.ScalarActualOpenConormal
