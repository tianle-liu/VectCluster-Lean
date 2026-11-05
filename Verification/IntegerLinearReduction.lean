/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimitiveLattice
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic

/-!
# Integer Linear Reduction

Reduction of actual integral linear maps in the standard free bases.
A primitive split injection remains injective modulo two.
-/
noncomputable section
namespace Verification.IntegerLinearReduction
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

def matrix (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) : Matrix κ ι ℤ := by
  classical
  exact LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne f

theorem matrix_entry (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) (i : κ) (j : ι) :
    matrix f i j = f (Finsupp.single j 1) i := by
  classical
  simp [matrix,LinearMap.toMatrix_apply]

theorem matrix_comp (f : (κ →₀ ℤ) →ₗ[ℤ] (τ →₀ ℤ))
    (g : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) : matrix (f.comp g) = matrix f * matrix g := by
  classical
  exact LinearMap.toMatrix_comp Finsupp.basisSingleOne Finsupp.basisSingleOne
    Finsupp.basisSingleOne f g

def reduce (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) : (ι → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2) := by
  classical
  exact Matrix.toLin' ((matrix f).map (Int.castRingHom (ZMod 2)))

theorem reduce_comp (f : (κ →₀ ℤ) →ₗ[ℤ] (τ →₀ ℤ))
    (g : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) : reduce (f.comp g) = (reduce f).comp (reduce g) := by
  classical
  simp only [reduce,matrix_comp,RingHom.mapMatrix_apply,Matrix.map_mul,Matrix.toLin'_mul]

theorem reduce_id : reduce (LinearMap.id : (ι →₀ ℤ) →ₗ[ℤ] (ι →₀ ℤ)) = LinearMap.id := by
  classical
  simp [reduce,matrix,LinearMap.toMatrix_id,Matrix.map_one]

theorem reduce_apply (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) (x : ι → ZMod 2) (i : κ) :
    reduce f x i = ∑ j, (f (Finsupp.single j 1) i : ZMod 2) * x j := by
  classical
  simp [reduce,Matrix.mulVec,dotProduct,matrix_entry]

theorem injective_of_split (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ))
    (r : (κ →₀ ℤ) →ₗ[ℤ] (ι →₀ ℤ)) (hr : r.comp f = LinearMap.id) :
    Function.Injective (reduce f) := by
  have h : (reduce r).comp (reduce f) = LinearMap.id := by
    rw [← reduce_comp,hr,reduce_id]
  exact (show Function.LeftInverse (reduce r) (reduce f) from
    fun x => LinearMap.congr_fun h x).injective

theorem injective_of_primitive (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ))
    (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    Function.Injective (reduce f) := by
  obtain ⟨e,he⟩ := Verification.PrimitiveLattice.primitive_columns_split_compatible f hf hs
  let r := (LinearMap.fst ℤ _ _).comp e.toLinearMap
  apply injective_of_split f r
  apply LinearMap.ext
  intro x
  exact congrArg Prod.fst (he x)

#print axioms matrix
#print axioms matrix_entry
#print axioms matrix_comp
#print axioms reduce
#print axioms reduce_comp
#print axioms reduce_id
#print axioms reduce_apply
#print axioms injective_of_split
#print axioms injective_of_primitive
end Verification.IntegerLinearReduction
