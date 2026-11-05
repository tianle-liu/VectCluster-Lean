/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BlockFixedCoordinates
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Block Residual Balance

The two residual degrees of a shifted closed/open block have their actual
survivor bases. Numerical rank balance then gives an explicit module
equivalence, which can be supplied to the proved finite pivot construction.
-/

namespace Verification.BlockResidualBalance

open Verification.GradedPerturbation Verification.PerturbedHomologyModel
  Verification.PathConeBlocks Verification.BlockFixedCoordinates

variable {R : Type*} [CommRing R]

noncomputable def dropRight {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (hn : ∀ x : N,x=0) : (M × N) ≃ₗ[R] M where
  toFun := Prod.fst
  invFun x := (x,0)
  left_inv x := Prod.ext rfl (hn x.2).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def dropLeft {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (hm : ∀ x : M,x=0) : (M × N) ≃ₗ[R] N where
  toFun := Prod.snd
  invFun x := (0,x)
  left_inv x := Prod.ext (hm x.1).symm rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (a : ι → ℤ) (b : κ → ℤ) (P : Matrix ι ι R) (Q : Matrix κ κ R)
variable (hP : ∀ i j,a i ≠ 0 → P i j=0) (hQ : ∀ i j,b i ≠ 0 → Q i j=0)

noncomputable def closedCoordinates :
    fixedModule (Sum.elim (fun i => a i-1) b) (diagonal P Q) (-1) ≃ₗ[R] fixedModule a P 0 :=
  (coordinates (fun i => a i-1) b P Q (-1)).trans
    (((shift a P (-1) (-1)).prodCongr (LinearEquiv.refl R (fixedModule b Q (-1)))).trans
      (dropRight (fun x => fixed_zero b Q hQ (-1) (by omega) x)))

noncomputable def openCoordinates :
    fixedModule (Sum.elim (fun i => a i-1) b) (diagonal P Q) 0 ≃ₗ[R] fixedModule b Q 0 :=
  (coordinates (fun i => a i-1) b P Q 0).trans
    (((shift a P 0 (-1)).prodCongr (LinearEquiv.refl R (fixedModule b Q 0))).trans
      (dropLeft (fun x => fixed_zero a P hP 1 (by omega) x)))

omit [Fintype ι] [Fintype κ] in
include hP hQ in
theorem diagonal_supported (i j : ι ⊕ κ)
    (hi : Sum.elim (fun i => a i-1) b i ≠ -1)
    (hi0 : Sum.elim (fun i => a i-1) b i ≠ 0) : diagonal P Q i j=0 := by
  cases i with
  | inl i =>
    cases j with
    | inl j => exact hP i j (by change a i-1 ≠ -1 at hi; omega)
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j => rfl
    | inr j => exact hQ i j hi0

omit [Fintype ι] [Fintype κ] in
noncomputable def basisBalance {C M N : Type*} [AddCommGroup C] [Module R C]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {c m n : ℕ} (bC : Basis (Fin c) R C) (bM : Basis (Fin m) R M)
    (bN : Basis (Fin n) R N) (h : c+n=m) : (C × N) ≃ₗ[R] M :=
  (bC.prod bN).equiv bM (finSumFinEquiv.trans (finCongr h))

noncomputable def balance {N : Type*} [AddCommGroup N] [Module R N]
    {c m n : ℕ} (bC : Basis (Fin c) R (fixedModule a P 0))
    (bM : Basis (Fin m) R (fixedModule b Q 0)) (bN : Basis (Fin n) R N) (h : c+n=m) :
    (fixedModule (Sum.elim (fun i => a i-1) b) (diagonal P Q) (-1) × N) ≃ₗ[R]
      fixedModule (Sum.elim (fun i => a i-1) b) (diagonal P Q) 0 :=
  (((closedCoordinates a b P Q hQ).prodCongr (LinearEquiv.refl R N)).trans
    (basisBalance bC bM bN h)).trans (openCoordinates a b P Q hP).symm

#print axioms dropRight
#print axioms dropLeft
#print axioms closedCoordinates
#print axioms openCoordinates
#print axioms diagonal_supported
#print axioms basisBalance
#print axioms balance

end Verification.BlockResidualBalance
