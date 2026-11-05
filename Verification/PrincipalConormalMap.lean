/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrincipalConormal
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Principal Conormal Map

The actual map on conormals of regular principal equations becomes
an isomorphism after extension of scalars when the equations map exactly
to one another. Its matrix in the original equation frames is 1.
-/
noncomputable section
universe u
namespace Verification.PrincipalConormalMap
open Verification.PrincipalConormal
open scoped TensorProduct
variable {A B : Type u} [CommRing A] [CommRing B]
variable (f : A →+* B) (x : A) (y : B) (hxy : f x = y)

include hxy in
theorem ideal_le : ideal x ≤ (ideal y).comap f := by
  apply Ideal.span_le.mpr
  intro z hz
  have hz' : z = x := Set.mem_singleton_iff.mp hz
  change f z ∈ ideal y
  rw [hz',hxy]
  exact Ideal.subset_span (Set.mem_singleton y)

def quotientMap : A ⧸ ideal x →+* B ⧸ ideal y :=
  Ideal.quotientMap (ideal y) f (ideal_le f x y hxy)

def quotientAlgebra : Algebra (A ⧸ ideal x) (B ⧸ ideal y) :=
  (quotientMap f x y hxy).toAlgebra

def cotangentMap : (ideal x).Cotangent →ₗ[ℤ] (ideal y).Cotangent :=
  Ideal.mapCotangent (ideal x) (ideal y) f.toIntAlgHom (ideal_le f x y hxy)

theorem cotangentMap_coordinate : cotangentMap f x y hxy (coordinate x) = coordinate y := by
  rw [cotangentMap,coordinate,Ideal.mapCotangent_toCotangent]
  apply congrArg (ideal y).toCotangent
  apply Subtype.ext
  exact hxy

def pullbackEquiv (hx : IsSMulRegular A x) (hy : IsSMulRegular B y) :
    letI := quotientAlgebra f x y hxy;
    (B ⧸ ideal y) ⊗[A ⧸ ideal x] (ideal x).Cotangent ≃ₗ[B ⧸ ideal y] (ideal y).Cotangent := by
  letI := quotientAlgebra f x y hxy
  exact ((basis x hx).baseChange (B ⧸ ideal y)).equiv (basis y hy) (Equiv.refl _)

theorem pullbackEquiv_coordinate (hx : IsSMulRegular A x) (hy : IsSMulRegular B y) :
    letI := quotientAlgebra f x y hxy;
    pullbackEquiv f x y hxy hx hy (1 ⊗ₜ[A ⧸ ideal x] coordinate x) = coordinate y := by
  letI := quotientAlgebra f x y hxy
  rw [← basis_apply x hx PUnit.unit,← Basis.baseChange_apply]
  rw [pullbackEquiv,Basis.equiv_apply,basis_apply]

theorem pullbackEquiv_tmul_coordinate (hx : IsSMulRegular A x) (hy : IsSMulRegular B y)
    (t : B ⧸ ideal y) :
    letI := quotientAlgebra f x y hxy;
    pullbackEquiv f x y hxy hx hy (t ⊗ₜ[A ⧸ ideal x] coordinate x) = t • coordinate y := by
  letI := quotientAlgebra f x y hxy
  have ht : t ⊗ₜ[A ⧸ ideal x] coordinate x = t • (1 ⊗ₜ[A ⧸ ideal x] coordinate x) := by
    rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  rw [ht,map_smul,pullbackEquiv_coordinate]

theorem pullbackEquiv_one_tmul (hx : IsSMulRegular A x) (hy : IsSMulRegular B y)
    (z : (ideal x).Cotangent) :
    letI := quotientAlgebra f x y hxy;
    pullbackEquiv f x y hxy hx hy (1 ⊗ₜ[A ⧸ ideal x] z) = cotangentMap f x y hxy z := by
  letI := quotientAlgebra f x y hxy
  have hz : (basis x hx).repr z PUnit.unit • coordinate x = z := by
    simpa only [basis_apply,Finset.univ_unique,Finset.sum_singleton] using (basis x hx).sum_repr z
  obtain ⟨a,ha⟩ := Ideal.Quotient.mk_surjective ((basis x hx).repr z PUnit.unit)
  rw [← ha] at hz
  rw [← hz,TensorProduct.tmul_smul,TensorProduct.smul_tmul']
  rw [pullbackEquiv_tmul_coordinate f x y hxy hx hy]
  change (Ideal.Quotient.mk (ideal y) (f a) * 1) • coordinate y =
    cotangentMap f x y hxy (a • coordinate x)
  rw [mul_one]
  change (f a) • (ideal y).toCotangent ⟨y,_⟩ =
    cotangentMap f x y hxy (a • (ideal x).toCotangent ⟨x,_⟩)
  rw [← map_smul,← map_smul,cotangentMap,Ideal.mapCotangent_toCotangent]
  apply congrArg (ideal y).toCotangent
  apply Subtype.ext
  change f a * y = f (a * x)
  rw [map_mul,hxy]

#print axioms ideal_le
#print axioms quotientMap
#print axioms quotientAlgebra
#print axioms cotangentMap
#print axioms cotangentMap_coordinate
#print axioms pullbackEquiv
#print axioms pullbackEquiv_coordinate
#print axioms pullbackEquiv_tmul_coordinate
#print axioms pullbackEquiv_one_tmul
end Verification.PrincipalConormalMap
