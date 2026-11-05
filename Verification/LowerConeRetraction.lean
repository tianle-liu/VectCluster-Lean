/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathPureContractionData
import Verification.PathConeGrading
import Verification.TransposeReduction

/-!
# Lower Cone Retraction

Actual finite cancellation of a lower triangular chain cone. The closed
block has degree shifted by -1. The constructed residual retains the exact
diagonal pure-survivor projector, with both support identities proved.
-/

namespace Verification.LowerConeRetraction

open Verification.FinitePerturbation Verification.GradedPerturbation
  Verification.PerturbedHomologyModel Verification.PathConeBlocks

variable {R ι κ : Type} [CommRing R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def degree (a : ι → ℤ) (b : κ → ℤ) : ι ⊕ κ → ℤ := Sum.elim (fun i => a i-1) b

def weight : ι ⊕ κ → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem shifted (a : ι → ℤ) (D : Matrix ι ι R) (k : ℤ) (hd : Homogeneous a k D) :
    Homogeneous (fun i => a i-1) k D := by
  intro i j hij
  exact hd i j (by change a i-1 ≠ a j-1+k at hij; omega)

structure Data (d : ι → ℤ) (D P : Matrix ι ι R) extends GradedRetraction d D P where
  right_support : differential*P=differential
  projection_degree : Homogeneous d 0 P
  projection_square : P*P=P

noncomputable def ofBlocks (a : ι → ℤ) (b : κ → ℤ)
    (A : Matrix ι ι R) (B : Matrix κ κ R) (C : Matrix κ ι R)
    (T : Verification.PathPureContractionData.Data a A)
    (U : Verification.PathPureContractionData.Data b B)
    (hd : Homogeneous (degree a b) 1 (Matrix.fromBlocks A 0 C B))
    (hD : Matrix.fromBlocks A 0 C B*Matrix.fromBlocks A 0 C B=0) :
    Data (degree a b) (Matrix.fromBlocks A 0 C B)
      (diagonal (pureProjection A T.homotopy) (pureProjection B U.homotopy)) := by
  let D₀ := diagonal A B
  let H := diagonal T.homotopy U.homotopy
  let V : Matrix (ι ⊕ κ) (ι ⊕ κ) R := Matrix.fromBlocks 0 0 C 0
  have he : D₀+V=Matrix.fromBlocks A 0 C B := by
    change Matrix.fromBlocks A 0 0 B+Matrix.fromBlocks 0 0 C 0=_
    rw [Matrix.fromBlocks_add]
    simp only [add_zero,zero_add]
  have hD₀ : D₀*D₀=0 := by
    rw [diagonal_mul,T.differential_square,U.differential_square,diagonal_zero]
  have hHH : H*H=0 := by rw [diagonal_mul,T.homotopy_square,U.homotopy_square,diagonal_zero]
  have hHDH : H*D₀*H=H := by rw [diagonal_mul,diagonal_mul,T.homotopy_regular,U.homotopy_regular]
  have hDHD : D₀*H*D₀=D₀ := by rw [diagonal_mul,diagonal_mul,T.generalized,U.generalized]
  have hdD₀ : Homogeneous (degree a b) 1 D₀ :=
    Verification.PathConeGrading.diagonal_homogeneous (fun i => a i-1) b 1 A B
      (shifted a A 1 T.differential_degree) U.differential_degree
  have hdH : Homogeneous (degree a b) (-1) H :=
    Verification.PathConeGrading.diagonal_homogeneous (fun i => a i-1) b (-1) _ _
      (shifted a T.homotopy (-1) T.homotopy_degree) U.homotopy_degree
  have hdV : Homogeneous (degree a b) 1 V := by
    intro i j hij
    cases i with
    | inl i => cases j <;> rfl
    | inr i =>
      cases j with
      | inl j => exact hd (Sum.inr i) (Sum.inl j) hij
      | inr j => rfl
  have hw : ∀ i : ι ⊕ κ,weight i≤1 := by intro i; cases i <;> simp [weight]
  have hWH : ∀ i j : ι ⊕ κ,weight i ≠ weight j → H i j=0 := by
    intro i j hij
    cases i <;> cases j <;> simp_all [weight,H,diagonal,Matrix.fromBlocks]
  have hWV : ∀ i j : ι ⊕ κ,weight i ≤ weight j → V i j=0 := by
    intro i j hij
    cases i <;> cases j <;> simp_all [weight,V,Matrix.fromBlocks]
  have hDD : (D₀+V)*(D₀+V)=0 := by rw [he]; exact hD
  let F := filteredRetraction (degree a b) D₀ H V hdD₀ hdH hdV hD₀ hHH hHDH hDHD hDD
    weight 1 hw hWH hWV
  have hPP := pureProjection_square D₀ H hD₀ hHH hHDH hDHD
  let E : Data (degree a b) (D₀+V) (pureProjection D₀ H) := {
    toGradedRetraction := F
    right_support := Verification.TransposeReduction.residual_right D₀ H V _ hPP
    projection_degree := Verification.PureDegreeSurvivors.projection_degree (degree a b) D₀ H hdD₀ hdH
    projection_square := hPP }
  have hp : pureProjection D₀ H=diagonal (pureProjection A T.homotopy) (pureProjection B U.homotopy) :=
    diagonal_projection A T.homotopy B U.homotopy
  rw [← he,← hp]
  exact E

#print axioms degree
#print axioms weight
#print axioms shifted
#print axioms Data
#print axioms ofBlocks

end Verification.LowerConeRetraction
