/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega

/-!
# Path Lattice

Integral mutable-row lattices of linear paths, in the even/odd vertex
ordering. The adjacent-difference matrix has a unimodular maximal minor.
The odd path image is exactly the kernel of the sum of odd coordinates;
its quotient is explicitly isomorphic to the integers. The even path
operator is an actual integral linear equivalence.
-/

namespace Verification.PathLattice

open Finset Matrix

/-- Lower bidiagonal path block. -/
def bidiagonal (m : ℕ) : Matrix (Fin m) (Fin m) ℤ := fun i j =>
  (if i.val = j.val then 1 else 0) - (if i.val = j.val + 1 then 1 else 0)

/-- Adjacent differences, including the two boundary terms. -/
def difference (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℤ := fun i j =>
  (if i = j.castSucc then 1 else 0) - (if i = j.succ then 1 else 0)

theorem difference_head (m : ℕ) (i j : Fin m) :
    difference m i.castSucc j = bidiagonal m i j := by
  simp only [difference, bidiagonal, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]

theorem bidiagonal_det (m : ℕ) : (bidiagonal m).det = 1 := by
  have hl : (bidiagonal m).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i.val < j.val := hij
    have hn : i.val ≠ j.val := by omega
    have hs : i.val ≠ j.val + 1 := by omega
    simp [bidiagonal, hn, hs]
  rw [Matrix.det_of_lowerTriangular _ hl]
  simp [bidiagonal]

/-- The path's consecutive matching gives an integral unit pivot. -/
noncomputable def bidiagonalEquiv (m : ℕ) : (Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ) :=
  Matrix.toLin'OfInv
    (Matrix.nonsing_inv_mul _ (by rw [bidiagonal_det]; exact isUnit_one))
    (Matrix.mul_nonsing_inv _ (by rw [bidiagonal_det]; exact isUnit_one))

theorem bidiagonalEquiv_apply (m : ℕ) (x : Fin m → ℤ) :
    bidiagonalEquiv m x = (bidiagonal m).mulVec x := rfl

theorem difference_head_mulVec (m : ℕ) (x : Fin m → ℤ) (i : Fin m) :
    (difference m).mulVec x i.castSucc = (bidiagonal m).mulVec x i := by
  simp only [Matrix.mulVec, dotProduct, difference_head]

theorem difference_column_sum (m : ℕ) (j : Fin m) : ∑ i, difference m i j = 0 := by
  simp [difference, Finset.sum_sub_distrib]

theorem difference_sum_zero (m : ℕ) (x : Fin m → ℤ) :
    ∑ i, (difference m).mulVec x i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, difference_column_sum, zero_mul, Finset.sum_const_zero]

/-- The rectangular path block is injective over the integers. -/
theorem difference_injective (m : ℕ) : Function.Injective (difference m).mulVec := by
  intro x y h
  apply (bidiagonalEquiv m).injective
  funext i
  have hi := congrFun h i.castSucc
  simpa only [difference_head_mulVec, bidiagonalEquiv_apply] using hi

/-- The primitive image statement, proved integrally rather than by rational rank. -/
theorem difference_image_iff (m : ℕ) (x : Fin (m + 1) → ℤ) :
    (∃ y, (difference m).mulVec y = x) ↔ ∑ i, x i = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact difference_sum_zero m y
  · intro hx
    let y := (bidiagonalEquiv m).symm (fun i => x i.castSucc)
    have hh (i : Fin m) : (difference m).mulVec y i.castSucc = x i.castSucc := by
      rw [difference_head_mulVec]
      exact congrFun ((bidiagonalEquiv m).apply_symm_apply (fun i => x i.castSucc)) i
    refine ⟨y, ?_⟩
    funext i
    refine Fin.lastCases ?_ (fun j => hh j) i
    have hz := difference_sum_zero m y
    rw [Fin.sum_univ_castSucc] at hx hz
    simp only [hh] at hz
    omega

/-- The transpose is surjective because its matching minor is unimodular. -/
theorem difference_transpose_surjective (m : ℕ) :
    Function.Surjective (difference m).transpose.mulVec := by
  have ht : Function.Surjective (bidiagonal m).transpose.mulVec := by
    apply Matrix.mulVec_surjective_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_transpose, bidiagonal_det]
    exact isUnit_one
  intro y
  obtain ⟨x, hx⟩ := ht y
  let v : Fin (m + 1) → ℤ := Fin.lastCases 0 x
  refine ⟨v, ?_⟩
  funext j
  change (∑ i, difference m i j * v i) = y j
  rw [Fin.sum_univ_castSucc]
  simp only [v, Fin.lastCases_last, mul_zero, zero_add, add_zero, Fin.lastCases_castSucc,
    difference_head]
  exact congrFun hx j

/-- Even path operator in parity order. -/
def evenOperator (m : ℕ) :
    ((Fin m → ℤ) × (Fin m → ℤ)) →ₗ[ℤ] ((Fin m → ℤ) × (Fin m → ℤ)) :=
  ((bidiagonal m).mulVecLin.comp (LinearMap.snd ℤ _ _)).prod
    (-((bidiagonal m).transpose.mulVecLin.comp (LinearMap.fst ℤ _ _)))

theorem bidiagonal_transpose_surjective (m : ℕ) :
    Function.Surjective (bidiagonal m).transpose.mulVec := by
  apply Matrix.mulVec_surjective_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_transpose, bidiagonal_det]
  exact isUnit_one

/-- The full even mutable operator is integrally surjective. -/
theorem evenOperator_surjective (m : ℕ) : Function.Surjective (evenOperator m) := by
  rintro ⟨x, y⟩
  obtain ⟨p, hp⟩ := bidiagonal_transpose_surjective m (-y)
  refine ⟨(p, (bidiagonalEquiv m).symm x), ?_⟩
  apply Prod.ext
  · exact (bidiagonalEquiv m).apply_symm_apply x
  · change -(bidiagonal m).transpose.mulVec p = y
    rw [hp, neg_neg]

/-- The even path row lattice is all of its integral coordinate module. -/
theorem even_range_eq_top (m : ℕ) : LinearMap.range (evenOperator m) = ⊤ :=
  LinearMap.range_eq_top.mpr (evenOperator_surjective m)

/-- Odd path operator in parity order; the first block consists of the odd vertices. -/
def oddOperator (m : ℕ) :
    ((Fin (m + 1) → ℤ) × (Fin m → ℤ)) →ₗ[ℤ]
      ((Fin (m + 1) → ℤ) × (Fin m → ℤ)) :=
  ((difference m).mulVecLin.comp (LinearMap.snd ℤ _ _)).prod
    (-((difference m).transpose.mulVecLin.comp (LinearMap.fst ℤ _ _)))

/-- Pairing with `(1,0,1,...,1)` in parity order. -/
def oddPairing (m : ℕ) : ((Fin (m + 1) → ℤ) × (Fin m → ℤ)) →ₗ[ℤ] ℤ where
  toFun x := ∑ i, x.1 i
  map_add' x y := Finset.sum_add_distrib
  map_smul' a x := by simp [Finset.mul_sum]

theorem odd_image_iff (m : ℕ) (x : (Fin (m + 1) → ℤ) × (Fin m → ℤ)) :
    x ∈ LinearMap.range (oddOperator m) ↔ oddPairing m x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact difference_sum_zero m y.2
  · intro hx
    obtain ⟨q, hq⟩ := (difference_image_iff m x.1).mpr hx
    obtain ⟨p, hp⟩ := difference_transpose_surjective m (-x.2)
    refine ⟨(p, q), ?_⟩
    apply Prod.ext
    · exact hq
    · change -(difference m).transpose.mulVec p = x.2
      rw [hp, neg_neg]

/-- Exact equality of the integral row lattice with a saturated kernel. -/
theorem odd_range_eq_ker (m : ℕ) :
    LinearMap.range (oddOperator m) = LinearMap.ker (oddPairing m) := by
  apply Submodule.ext
  intro x
  exact odd_image_iff m x

theorem oddPairing_surjective (m : ℕ) : Function.Surjective (oddPairing m) := by
  intro z
  refine ⟨(Pi.single (Fin.last m) z, 0), ?_⟩
  simp [oddPairing]

/-- The actual integral cokernel is the integers, with no torsion. -/
noncomputable def oddCokernelEquiv (m : ℕ) :
    (((Fin (m + 1) → ℤ) × (Fin m → ℤ)) ⧸ LinearMap.range (oddOperator m)) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (odd_range_eq_ker m)).trans
    (LinearMap.quotKerEquivOfSurjective (oddPairing m) (oddPairing_surjective m))

/-- The consecutive skew adjacency matrix of a linearly oriented path. -/
def pathMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  (if j.val = i.val + 1 then 1 else 0) - (if i.val = j.val + 1 then 1 else 0)

/-- The even path matrix after moving odd-numbered vertices before even-numbered vertices. -/
def evenMatrix (m : ℕ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℤ :=
  Matrix.fromBlocks 0 (bidiagonal m) (-(bidiagonal m).transpose) 0

/-- The same parity ordering for an odd path. -/
def oddMatrix (m : ℕ) : Matrix (Fin (m+1) ⊕ Fin m) (Fin (m+1) ⊕ Fin m) ℤ :=
  Matrix.fromBlocks 0 (difference m) (-(difference m).transpose) 0

def evenVertex (m : ℕ) : (Fin m ⊕ Fin m) → Fin (2*m)
  | Sum.inl i => ⟨2*i.val, by omega⟩
  | Sum.inr j => ⟨2*j.val+1, by omega⟩

def oddVertex (m : ℕ) : (Fin (m+1) ⊕ Fin m) → Fin (2*m+1)
  | Sum.inl i => ⟨2*i.val, by omega⟩
  | Sum.inr j => ⟨2*j.val+1, by omega⟩

theorem evenVertex_bijective (m : ℕ) : Function.Bijective (evenVertex m) := by
  constructor
  · intro v w h
    have hv := congrArg Fin.val h
    cases v <;> cases w
    all_goals simp only [evenVertex] at hv
    · apply congrArg Sum.inl; apply Fin.ext; omega
    · omega
    · omega
    · apply congrArg Sum.inr; apply Fin.ext; omega
  · intro i
    by_cases hi : i.val % 2 = 0
    · refine ⟨Sum.inl ⟨i.val / 2, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [evenVertex]
      omega
    · refine ⟨Sum.inr ⟨i.val / 2, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [evenVertex]
      omega

theorem oddVertex_bijective (m : ℕ) : Function.Bijective (oddVertex m) := by
  constructor
  · intro v w h
    have hv := congrArg Fin.val h
    cases v <;> cases w
    all_goals simp only [oddVertex] at hv
    · apply congrArg Sum.inl; apply Fin.ext; omega
    · omega
    · omega
    · apply congrArg Sum.inr; apply Fin.ext; omega
  · intro i
    by_cases hi : i.val % 2 = 0
    · refine ⟨Sum.inl ⟨i.val / 2, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [oddVertex]
      omega
    · refine ⟨Sum.inr ⟨i.val / 2, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [oddVertex]
      omega

noncomputable def evenReindex (m : ℕ) : (Fin m ⊕ Fin m) ≃ Fin (2*m) :=
  Equiv.ofBijective (evenVertex m) (evenVertex_bijective m)

noncomputable def oddReindex (m : ℕ) : (Fin (m+1) ⊕ Fin m) ≃ Fin (2*m+1) :=
  Equiv.ofBijective (oddVertex m) (oddVertex_bijective m)

/-- Exact source correspondence with the consecutively indexed even path matrix. -/
theorem evenMatrix_reindex (m : ℕ) :
    (pathMatrix (2*m)).submatrix (evenReindex m) (evenReindex m) = evenMatrix m := by
  ext i j
  cases i <;> cases j
  all_goals
    simp only [Matrix.submatrix_apply, evenReindex, Equiv.ofBijective_apply,
      pathMatrix, evenVertex, evenMatrix, Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
      Matrix.zero_apply, Matrix.neg_apply, Matrix.transpose_apply, bidiagonal]
    split_ifs <;> omega

/-- Exact source correspondence with the consecutively indexed odd path matrix. -/
theorem oddMatrix_reindex (m : ℕ) :
    (pathMatrix (2*m+1)).submatrix (oddReindex m) (oddReindex m) = oddMatrix m := by
  ext i j
  cases i <;> cases j
  all_goals
    simp only [Matrix.submatrix_apply, oddReindex, Equiv.ofBijective_apply,
      pathMatrix, oddVertex, oddMatrix, Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
      Matrix.zero_apply, Matrix.neg_apply, Matrix.transpose_apply, difference,
      Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
    split_ifs <;> omega

/-- The parity-block matrix acts by the independently defined even operator. -/
theorem evenMatrix_action (m : ℕ) (x y : Fin m → ℤ) :
    (evenMatrix m).mulVec (Sum.elim x y) =
      Sum.elim (evenOperator m (x,y)).1 (evenOperator m (x,y)).2 := by
  simp [evenMatrix, Matrix.fromBlocks_mulVec, evenOperator, Function.comp_def, Matrix.neg_mulVec, Matrix.mulVec_transpose]

/-- The parity-block matrix acts by the independently defined odd operator. -/
theorem oddMatrix_action (m : ℕ) (x : Fin (m+1) → ℤ) (y : Fin m → ℤ) :
    (oddMatrix m).mulVec (Sum.elim x y) =
      Sum.elim (oddOperator m (x,y)).1 (oddOperator m (x,y)).2 := by
  simp [oddMatrix, Matrix.fromBlocks_mulVec, oddOperator, Function.comp_def, Matrix.neg_mulVec, Matrix.mulVec_transpose]

/-- Unimodularity of the actual even path matrix over the integers. -/
theorem even_path_unimodular (m : ℕ) : IsUnit (pathMatrix (2*m)).det := by
  rw [← Matrix.det_submatrix_equiv_self (evenReindex m), evenMatrix_reindex]
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  intro y
  obtain ⟨⟨p,q⟩, hpq⟩ := evenOperator_surjective m (y ∘ Sum.inl, y ∘ Sum.inr)
  refine ⟨Sum.elim p q, ?_⟩
  rw [evenMatrix_action, hpq]
  funext i
  cases i <;> rfl

/-- The even integral path operator as an explicit linear equivalence. -/
noncomputable def evenPathEquiv (m : ℕ) : (Fin (2*m) → ℤ) ≃ₗ[ℤ] (Fin (2*m) → ℤ) :=
  Matrix.toLin'OfInv (Matrix.nonsing_inv_mul _ (even_path_unimodular m))
    (Matrix.mul_nonsing_inv _ (even_path_unimodular m))

/-- Actual integral coordinate reordering. -/
noncomputable def oddCoordinates (m : ℕ) : (Fin (2*m+1) → ℤ) ≃ₗ[ℤ]
    ((Fin (m+1) → ℤ) × (Fin m → ℤ)) :=
  (LinearEquiv.funCongrLeft ℤ ℤ (oddReindex m)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ ℤ ℤ)

/-- Pairing with alternating ones and zeroes in the consecutive vertex order. -/
noncomputable def pathPairing (m : ℕ) : (Fin (2*m+1) → ℤ) →ₗ[ℤ] ℤ :=
  (oddPairing m).comp (oddCoordinates m).toLinearMap

theorem pathPairing_formula (m : ℕ) (x : Fin (2*m+1) → ℤ) :
    pathPairing m x = ∑ i : Fin (m+1), x ⟨2*i.val, by omega⟩ := rfl

theorem odd_coordinate_transport (m : ℕ) (x : Fin (2*m+1) → ℤ) :
    oddCoordinates m ((pathMatrix (2*m+1)).mulVec x) =
      oddOperator m (oddCoordinates m x) := by
  have h := Matrix.submatrix_mulVec_equiv (pathMatrix (2*m+1))
    (x ∘ oddReindex m) (oddReindex m) (oddReindex m)
  have hcomp : (x ∘ oddReindex m) ∘ (oddReindex m).symm = x := by
    funext i
    simp
  rw [oddMatrix_reindex, hcomp] at h
  have hv : Sum.elim (oddCoordinates m x).1 (oddCoordinates m x).2 = x ∘ oddReindex m := by
    funext i
    cases i <;> rfl
  have hb := oddMatrix_action m (oddCoordinates m x).1 (oddCoordinates m x).2
  rw [hv, h] at hb
  apply Prod.ext
  · funext i
    exact congrFun hb (Sum.inl i)
  · funext i
    exact congrFun hb (Sum.inr i)

/-- The exact consecutive-coordinate image, not merely a rank computation. -/
theorem odd_path_image_iff (m : ℕ) (x : Fin (2*m+1) → ℤ) :
    x ∈ LinearMap.range (pathMatrix (2*m+1)).mulVecLin ↔ pathPairing m x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    change oddPairing m (oddCoordinates m ((pathMatrix (2*m+1)).mulVec y)) = 0
    rw [odd_coordinate_transport]
    exact (odd_image_iff m _).mp ⟨oddCoordinates m y, rfl⟩
  · intro hx
    obtain ⟨y, hy⟩ := (odd_image_iff m (oddCoordinates m x)).mpr hx
    refine ⟨(oddCoordinates m).symm y, ?_⟩
    apply (oddCoordinates m).injective
    change oddCoordinates m ((pathMatrix (2*m+1)).mulVec ((oddCoordinates m).symm y)) = _
    rw [odd_coordinate_transport, LinearEquiv.apply_symm_apply, hy]

theorem odd_path_range_eq_ker (m : ℕ) :
    LinearMap.range (pathMatrix (2*m+1)).mulVecLin = LinearMap.ker (pathPairing m) := by
  apply Submodule.ext
  intro x
  exact odd_path_image_iff m x

theorem pathPairing_surjective (m : ℕ) : Function.Surjective (pathPairing m) :=
  (oddPairing_surjective m).comp (oddCoordinates m).surjective

/-- Cokernel of the literal odd path matrix, via the alternating-coordinate pairing. -/
noncomputable def oddPathCokernelEquiv (m : ℕ) :
    ((Fin (2*m+1) → ℤ) ⧸ LinearMap.range (pathMatrix (2*m+1)).mulVecLin) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (odd_path_range_eq_ker m)).trans
    (LinearMap.quotKerEquivOfSurjective (pathPairing m) (pathPairing_surjective m))

/-- Saturation is explicit over the integers. -/
theorem odd_path_saturated (m : ℕ) (k : ℤ) (hk : k ≠ 0) (x : Fin (2*m+1) → ℤ)
    (hx : k • x ∈ LinearMap.range (pathMatrix (2*m+1)).mulVecLin) :
    x ∈ LinearMap.range (pathMatrix (2*m+1)).mulVecLin := by
  apply (odd_path_image_iff m x).mpr
  have h := (odd_path_image_iff m (k • x)).mp hx
  rw [map_smul, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hk

/-- Explicit coordinates on the rank-`2m` image of an odd path. -/
def imageParameter (m : ℕ) :
    ((Fin m → ℤ) × (Fin m → ℤ)) →ₗ[ℤ] ((Fin (m+1) → ℤ) × (Fin m → ℤ)) :=
  (difference m).mulVecLin.prodMap LinearMap.id

theorem imageParameter_injective (m : ℕ) : Function.Injective (imageParameter m) := by
  intro x y h
  apply Prod.ext
  · exact difference_injective m (congrArg Prod.fst h)
  · have hs := congrArg Prod.snd h
    exact hs

theorem imageParameter_range (m : ℕ) :
    LinearMap.range (imageParameter m) = LinearMap.range (oddOperator m) := by
  apply Submodule.ext
  intro x
  rw [odd_image_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact difference_sum_zero m y.1
  · intro hx
    obtain ⟨y, hy⟩ := (difference_image_iff m x.1).mpr hx
    exact ⟨(y, x.2), Prod.ext hy rfl⟩

/-- An actual integral basis parameterization establishes rank `n-1`. -/
noncomputable def oddImageEquiv (m : ℕ) :
    ((Fin m → ℤ) × (Fin m → ℤ)) ≃ₗ[ℤ] LinearMap.range (oddOperator m) :=
  (LinearEquiv.ofInjective (imageParameter m) (imageParameter_injective m)).trans
    (LinearEquiv.ofEq _ _ (imageParameter_range m))

/-- The mutable row lattice as the image of the transpose, over the integers. -/
def rowLattice (n : ℕ) : Submodule ℤ (Fin n → ℤ) :=
  LinearMap.range (pathMatrix n).transpose.mulVecLin

theorem pathMatrix_transpose (n : ℕ) : (pathMatrix n).transpose = -pathMatrix n := by
  ext i j
  simp [pathMatrix, neg_sub]

theorem rowLattice_eq_range (n : ℕ) :
    rowLattice n = LinearMap.range (pathMatrix n).mulVecLin := by
  have h : (pathMatrix n).transpose.mulVecLin = -(pathMatrix n).mulVecLin := by
    apply LinearMap.ext
    intro x
    change (pathMatrix n).transpose.mulVec x = - (pathMatrix n).mulVec x
    rw [pathMatrix_transpose, Matrix.neg_mulVec]
  rw [rowLattice, h, LinearMap.range_neg]

/-- The article's even-path mutable-row-lattice assertion. -/
theorem even_rowLattice (m : ℕ) : rowLattice (2*m) = ⊤ := by
  rw [rowLattice_eq_range]
  apply LinearMap.range_eq_top.mpr
  apply Matrix.mulVec_surjective_iff_isUnit.mpr
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (even_path_unimodular m)

/-- The article's odd-path mutable-row-lattice assertion, with the explicit pairing. -/
theorem odd_rowLattice (m : ℕ) :
    rowLattice (2*m+1) = LinearMap.ker (pathPairing m) := by
  rw [rowLattice_eq_range, odd_path_range_eq_ker]

/-- The literal mutable row-lattice quotient, not a rational vector-space quotient. -/
noncomputable def oddRowQuotientEquiv (m : ℕ) :
    ((Fin (2*m+1) → ℤ) ⧸ rowLattice (2*m+1)) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (odd_rowLattice m)).trans
    (LinearMap.quotKerEquivOfSurjective (pathPairing m) (pathPairing_surjective m))

/-- The explicit vertex reordering identifies the literal row lattice with the parity image. -/
theorem odd_rowLattice_coordinates (m : ℕ) :
    (rowLattice (2*m+1)).map (oddCoordinates m).toLinearMap =
      LinearMap.range (oddOperator m) := by
  rw [odd_rowLattice, odd_range_eq_ker]
  apply Submodule.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨(oddCoordinates m).symm y, ?_, (oddCoordinates m).apply_symm_apply y⟩
    change oddPairing m (oddCoordinates m ((oddCoordinates m).symm y)) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact hy

/-- A literal integral basis parameterization of the mutable row lattice, of rank `2m`. -/
noncomputable def oddRowBasisEquiv (m : ℕ) :
    ((Fin m → ℤ) × (Fin m → ℤ)) ≃ₗ[ℤ] rowLattice (2*m+1) :=
  (oddImageEquiv m).trans
    ((oddCoordinates m).ofSubmodules _ _ (odd_rowLattice_coordinates m)).symm

/-- An explicit left inverse for the rectangular odd-path matching block. -/
noncomputable def differenceRetraction (m : ℕ) : (Fin (m+1) → ℤ) →ₗ[ℤ] (Fin m → ℤ) :=
  (bidiagonalEquiv m).symm.toLinearMap.comp (LinearMap.funLeft ℤ ℤ Fin.castSucc)

theorem differenceRetraction_leftInverse (m : ℕ) :
    (differenceRetraction m).comp (difference m).mulVecLin = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (bidiagonalEquiv m).symm (fun i => (difference m).mulVec x i.castSucc) = x
  have he : (fun i => (difference m).mulVec x i.castSucc) = bidiagonalEquiv m x := by
    funext i
    exact difference_head_mulVec m x i
  rw [he, LinearEquiv.symm_apply_apply]

section BipartiteExtension

variable {R P Q Z : Type*} [CommRing R]
variable [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
variable [AddCommGroup Z] [Module R Z]

/-- The full extended bipartite matrix, with mutable blocks `D,E` and frozen blocks `C,F`. -/
def bipartiteExtension (D : Q →ₗ[R] P) (E : P →ₗ[R] Q)
    (C : P →ₗ[R] Z) (F : Q →ₗ[R] Z) : (P × Q) →ₗ[R] (P × (Q × Z)) :=
  (D.comp (LinearMap.snd R P Q)).prod
    ((E.comp (LinearMap.fst R P Q)).prod
      (C.comp (LinearMap.fst R P Q) + F.comp (LinearMap.snd R P Q)))

/-- Explicit recovery of both column families from the matching block and the AS splitting. -/
def extensionRetraction (J : P →ₗ[R] Q) (L : (Q × Z) →ₗ[R] P) (F : Q →ₗ[R] Z) :
    (P × (Q × Z)) →ₗ[R] (P × Q) :=
  (L.comp ((LinearMap.fst R Q Z |>.comp (LinearMap.snd R P (Q × Z))).prod
    ((LinearMap.snd R Q Z |>.comp (LinearMap.snd R P (Q × Z))) -
      F.comp (J.comp (LinearMap.fst R P (Q × Z)))))).prod
    (J.comp (LinearMap.fst R P (Q × Z)))

/-- AS on the larger bipartition, as a supplied actual splitting, gives a splitting of all columns. -/
theorem bipartiteExtension_split (D : Q →ₗ[R] P) (E : P →ₗ[R] Q)
    (C : P →ₗ[R] Z) (F : Q →ₗ[R] Z)
    (J : P →ₗ[R] Q) (L : (Q × Z) →ₗ[R] P)
    (hJ : J.comp D = LinearMap.id) (hL : L.comp (E.prod C) = LinearMap.id) :
    (extensionRetraction J L F).comp (bipartiteExtension D E C F) = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨p,q⟩
  have hJq := LinearMap.congr_fun hJ q
  have hLp := LinearMap.congr_fun hL p
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.prod_apply] at hJq hLp
  change L (E p, C p) = p at hLp
  apply Prod.ext <;> simp [extensionRetraction, bipartiteExtension, hJq, hLp]

/-- In particular, the full extended matrix has independent columns. -/
theorem bipartiteExtension_injective (D : Q →ₗ[R] P) (E : P →ₗ[R] Q)
    (C : P →ₗ[R] Z) (F : Q →ₗ[R] Z)
    (J : P →ₗ[R] Q) (L : (Q × Z) →ₗ[R] P)
    (hJ : J.comp D = LinearMap.id) (hL : L.comp (E.prod C) = LinearMap.id) :
    Function.Injective (bipartiteExtension D E C F) := by
  apply Function.LeftInverse.injective (g := extensionRetraction J L F)
  intro x
  exact LinearMap.congr_fun (bipartiteExtension_split D E C F J L hJ hL) x

end BipartiteExtension

#print axioms bidiagonal
#print axioms difference
#print axioms difference_head
#print axioms bidiagonal_det
#print axioms bidiagonalEquiv
#print axioms bidiagonalEquiv_apply
#print axioms difference_head_mulVec
#print axioms difference_column_sum
#print axioms difference_sum_zero
#print axioms difference_injective
#print axioms difference_image_iff
#print axioms difference_transpose_surjective
#print axioms evenOperator
#print axioms oddOperator
#print axioms oddPairing
#print axioms odd_image_iff
#print axioms odd_range_eq_ker
#print axioms oddPairing_surjective
#print axioms oddCokernelEquiv

#print axioms bidiagonal_transpose_surjective
#print axioms evenOperator_surjective
#print axioms even_range_eq_top

#print axioms pathMatrix
#print axioms evenMatrix
#print axioms oddMatrix
#print axioms evenVertex
#print axioms oddVertex
#print axioms evenVertex_bijective
#print axioms oddVertex_bijective
#print axioms evenReindex
#print axioms oddReindex
#print axioms evenMatrix_reindex
#print axioms oddMatrix_reindex
#print axioms evenMatrix_action
#print axioms oddMatrix_action
#print axioms even_path_unimodular

#print axioms evenPathEquiv
#print axioms oddCoordinates
#print axioms pathPairing
#print axioms pathPairing_formula
#print axioms odd_coordinate_transport
#print axioms odd_path_image_iff
#print axioms odd_path_range_eq_ker
#print axioms pathPairing_surjective
#print axioms oddPathCokernelEquiv
#print axioms odd_path_saturated
#print axioms imageParameter
#print axioms imageParameter_injective
#print axioms imageParameter_range
#print axioms oddImageEquiv

#print axioms rowLattice
#print axioms pathMatrix_transpose
#print axioms rowLattice_eq_range
#print axioms even_rowLattice
#print axioms odd_rowLattice
#print axioms oddRowQuotientEquiv

#print axioms differenceRetraction
#print axioms differenceRetraction_leftInverse
#print axioms bipartiteExtension
#print axioms extensionRetraction
#print axioms bipartiteExtension_split
#print axioms bipartiteExtension_injective

#print axioms odd_rowLattice_coordinates
#print axioms oddRowBasisEquiv

end Verification.PathLattice
