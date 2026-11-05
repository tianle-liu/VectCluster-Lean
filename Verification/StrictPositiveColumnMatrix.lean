/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictPositiveColumnAssembly

/-!
# Strict Positive Column Matrix

Positive scalar columns assemble into their literal biproduct matrix; the separate integer target column is zero.
-/
noncomputable section
namespace Verification.StrictPositiveColumnMatrix
open Classical CategoryTheory CategoryTheory.Limits
open Verification.StrictTorusSymbolInput Verification.BinaryWordCoordinates
attribute [local instance] Abelian.hasFiniteBiproducts
open scoped BigOperators
variable {A : Type*} [Category A] [Abelian A]
variable (Z₀ : A) (M : ℤ → A) (r n s m : ℕ) {X Y : A}
variable (ex : X ≅ ⨁ (summand Z₀ M r n)) (ey : Y ≅ ⨁ (summand Z₀ M s m))
variable (hr : ∀ k : Index n,degree r n k≠0)
variable (a : ∀ (k : Index n) (i : Index m),degree s m i≠0 → (M (degree r n k) ⟶ M (degree s m i)))

def entries (k : Index n) (i : Index m) : summand Z₀ M r n k ⟶ summand Z₀ M s m i :=
  if hi : degree s m i=0 then 0 else
    eqToHom (if_neg (hr k)) ≫ a k i hi ≫ eqToHom (if_neg hi).symm

def column (i : Index m) (hi : degree s m i≠0) : X ⟶ M (degree s m i) :=
  ∑ k : Index n, ex.hom ≫ biproduct.π _ k ≫ eqToHom (if_neg (hr k)) ≫ a k i hi

theorem matrix :
    StrictPositiveColumnAssembly.arrow Z₀ M s m ey (column Z₀ M r n s m ex hr a)=
      ex.hom ≫ biproduct.matrix (entries Z₀ M r n s m hr a) ≫ ey.inv := by
  apply (cancel_mono ey.hom).1
  apply (cancel_epi ex.inv).1
  apply biproduct.hom_ext'
  intro k
  apply biproduct.hom_ext
  intro i
  by_cases hi : degree s m i=0
  · simp [StrictPositiveColumnAssembly.arrow,entries,hi,Category.assoc,biproduct.ι_matrix_assoc]
  · simp [StrictPositiveColumnAssembly.arrow,entries,column,hi,Category.assoc,
      Preadditive.comp_sum,Preadditive.sum_comp,biproduct.ι_matrix_assoc,biproduct.ι_π_assoc]
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · simp

#print axioms entries
#print axioms column
#print axioms matrix
end Verification.StrictPositiveColumnMatrix
