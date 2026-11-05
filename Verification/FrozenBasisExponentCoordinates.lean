/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Matrix.Mul

/-!
# Frozen Basis Exponent Coordinates

A chosen basis of frozen rows induces the contragredient coordinate
change on frozen character exponents. The row matrix action is proved,
so a row-basis change is not confused with its inverse or transpose.
-/
noncomputable section
namespace Verification.FrozenBasisExponentCoordinates
open Classical
open scoped BigOperators
variable {F N V : Type*} [Fintype F] [Fintype N]
variable (b : Basis N ℤ (F → ℤ))

def coordinates : (F → ℤ) ≃ₗ[ℤ] (N → ℤ) :=
  (Pi.basisFun ℤ F).toDualEquiv.trans b.dualBasis.equivFun

omit [Fintype N] in
theorem pi_dual (x y : F → ℤ) : (Pi.basisFun ℤ F).toDual x y=∑ f,x f*y f := by
  have hy : y=∑ f,y f • (Pi.basisFun ℤ F) f := by
    simpa only [Pi.basisFun_repr] using ((Pi.basisFun ℤ F).sum_repr y).symm
  conv_lhs => rw [hy,map_sum]
  simp only [map_smul,Basis.toDual_apply_left,Pi.basisFun_repr,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro f _
  exact mul_comm _ _

theorem coordinates_apply (x : F → ℤ) (n : N) : coordinates b x n=∑ f,b n f*x f := by
  rw [coordinates,LinearEquiv.trans_apply,Basis.dualBasis_equivFun,Basis.toDualEquiv_apply,pi_dual]
  apply Finset.sum_congr rfl
  intro f _
  exact mul_comm _ _

theorem column_coordinates (C : Matrix F V ℤ) (i : V) :
    coordinates b (fun f=>C f i)=fun n=>C.transpose.mulVec (b n) i := by
  funext n
  rw [coordinates_apply]
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,mul_comm]

#print axioms coordinates
#print axioms pi_dual
#print axioms coordinates_apply
#print axioms column_coordinates
end Verification.FrozenBasisExponentCoordinates
