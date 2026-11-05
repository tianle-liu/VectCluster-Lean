/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalGlobalGenerators
import Verification.PathEndpointMonomials
import Verification.LaurentPolynomialUniversal

/-!
# Path Original Z Presentation

The literal Z path has one frozen coordinate in the first positive
exchange monomial. Its coefficient Laurent parameter is that actual frozen
unit, and all mutable and partner generators are preserved.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
namespace Verification.PathOriginalZPresentation
open Verification.FrozenAcyclicCover Verification.PathPresentation
open Verification.PathAdjacencyMonomials Verification.PathEndpointMonomials
open scoped BigOperators

def matrix (n : ℕ) : (Fin n ⊕ Fin 1) → (Fin n ⊕ Empty) → ℤ :=
  fun a => Sum.elim (fun i => Sum.elim (fun k => PathLattice.pathMatrix n k i)
    (fun _ => if i.val=0 then 1 else 0) a) Empty.elim

variable {T : Type} [CommRing T] {n : ℕ}

#print axioms matrix

theorem exchange_sum (xx : Fin n → T) (t : T) (i : Fin n) :
    (∏ a : Fin n ⊕ Fin 1, Sum.elim xx (fun _=>t) a ^ (matrix n a (Sum.inl i)).toNat)+
      (∏ a : Fin n ⊕ Fin 1, Sum.elim xx (fun _=>t) a ^ (-matrix n a (Sum.inl i)).toNat)=
        boundary t 1 xx i.castSucc.castSucc+boundary t 1 xx i.succ.succ := by
  simp only [Fintype.prod_sum_type,matrix,Sum.elim_inl,Sum.elim_inr,Fintype.prod_unique,
    positive_product,negative_product]
  have h₁ := PathEndpointMonomials.previous_boundary t 1 xx i
  have h₂ := PathEndpointMonomials.next_boundary t 1 xx i
  by_cases hi : i.val=0
  · simp only [hi,↓reduceIte,Int.toNat_one,show ((-1:ℤ).toNat)=0 by decide,pow_one,pow_zero,mul_one] at *
    rw [← h₁,← h₂]
    simp only [ite_self,one_mul]
    rw [mul_comm]
  · simp only [hi,↓reduceIte,Int.toNat_zero,neg_zero,pow_zero,mul_one] at *
    rw [← h₁,← h₂]
    simp only [ite_self,one_mul]

variable (R : Type) [CommRing R] (n : ℕ)
#print axioms exchange_sum

abbrev Coefficient := LaurentBasepoint.Laurent R
#print axioms Coefficient

abbrev Path := PathAlgebra n (LaurentPolynomialUniversal.parameter R) 1
#print axioms Path

abbrev Original := Global R (Fin 1) n (matrix n)

#print axioms Original

def originalX (i : Fin n) : Original R n := initial R (Fin 1) n (matrix n) (Sum.inl i)
#print axioms originalX

def originalY (i : Fin n) : Original R n := mutated R (Fin 1) n (matrix n) i
#print axioms originalY

def originalParameter : Original R n := initial R (Fin 1) n (matrix n) (Sum.inr 0)

#print axioms originalParameter

def frozenUnit : (Original R n)ˣ := (frozen_unit R (Fin 1) n (matrix n) 0).unit

#print axioms frozenUnit

theorem frozenUnit_val : (frozenUnit R n : Original R n)=originalParameter R n :=
  (frozen_unit R (Fin 1) n (matrix n) 0).unit_spec

#print axioms frozenUnit_val

def coefficientMap : Coefficient R →ₐ[R] Original R n :=
  LaurentPolynomialUniversal.lift (Algebra.ofId R (Original R n)) (frozenUnit R n)

#print axioms coefficientMap

theorem coefficient_parameter : coefficientMap R n (LaurentPolynomialUniversal.parameter R)=originalParameter R n := by
  rw [coefficientMap,LaurentPolynomialUniversal.lift_parameter,frozenUnit_val]

#print axioms coefficient_parameter

instance coefficientAlgebra : Algebra (Coefficient R) (Original R n) := (coefficientMap R n).toRingHom.toAlgebra
#print axioms coefficientAlgebra

instance coefficientTower : IsScalarTower R (Coefficient R) (Original R n) := IsScalarTower.of_algHom (coefficientMap R n)

#print axioms coefficientTower

theorem original_equations : Equations (originalParameter R n) 1 (originalX R n) (originalY R n) := by
  intro i
  have hh := literal_equation R (Fin 1) n (matrix n) i
  have he : initial R (Fin 1) n (matrix n)=Sum.elim (originalX R n) (fun _=>originalParameter R n) := by
    funext a
    cases a with
    | inl a => rfl
    | inr a => have ha : a=0 := Subsingleton.elim _ _; subst a; rfl
  change originalX R n i*originalY R n i=_ at hh
  rw [he,exchange_sum] at hh
  exact hh

#print axioms original_equations

def pathMap : Path R n →ₐ[Coefficient R] Original R n :=
  PathPresentation.lift _ _ (originalX R n) (originalY R n) (by
    change Equations (coefficientMap R n (LaurentPolynomialUniversal.parameter R))
      (algebraMap (Coefficient R) (Original R n) 1) _ _
    rw [coefficient_parameter,map_one]
    exact original_equations R n)

#print axioms pathMap

def toOriginal : Path R n →ₐ[R] Original R n := (pathMap R n).restrictScalars R

#print axioms toOriginal

def pathOriginals : Fin n ⊕ Fin 1 → Path R n :=
  Sum.elim (x (LaurentPolynomialUniversal.parameter R) 1)
    (fun _=>algebraMap (Coefficient R) (Path R n) (LaurentPolynomialUniversal.parameter R))

#print axioms pathOriginals

theorem path_equations (i : Fin n) :
    pathOriginals R n (Sum.inl i) * y (LaurentPolynomialUniversal.parameter R) 1 i =
      (∏ a,pathOriginals R n a ^ (matrix n a (Sum.inl i)).toNat) +
        ∏ a,pathOriginals R n a ^ (-matrix n a (Sum.inl i)).toNat := by
  unfold pathOriginals
  rw [exchange_sum]
  simpa only [Sum.elim_inl, map_one] using equations n (LaurentPolynomialUniversal.parameter R) (1:Coefficient R) i

#print axioms path_equations

theorem path_frozen_unit (k : Fin 1) : IsUnit (pathOriginals R n (Sum.inr k)) := by
  change IsUnit (algebraMap (Coefficient R) (Path R n) (LaurentPolynomialUniversal.parameter R))
  simpa only [LaurentPolynomialUniversal.parameterUnit_val] using
    (LaurentPolynomialUniversal.parameterUnit R).isUnit.map (algebraMap (Coefficient R) (Path R n))

#print axioms path_frozen_unit

def toPath : Original R n →ₐ[R] Path R n where
  __ := OriginalGlobalGenerators.lift (S := Path R n) R (Fin 1) n (matrix n)
    (algebraMap R (Path R n)) (pathOriginals R n) (y (LaurentPolynomialUniversal.parameter R) 1)
    (path_equations R n) (path_frozen_unit R n)
  commutes' := OriginalGlobalGenerators.lift_scalar (S := Path R n) R (Fin 1) n (matrix n)
    (algebraMap R (Path R n)) (pathOriginals R n) (y (LaurentPolynomialUniversal.parameter R) 1)
    (path_equations R n) (path_frozen_unit R n)

#print axioms toPath

theorem toOriginal_x (i : Fin n) : toOriginal R n (x (LaurentPolynomialUniversal.parameter R) 1 i)=originalX R n i := by
  simp only [toOriginal, AlgHom.restrictScalars_apply, pathMap, PathPresentation.lift_x]

#print axioms toOriginal_x

theorem toOriginal_y (i : Fin n) : toOriginal R n (y (LaurentPolynomialUniversal.parameter R) 1 i)=originalY R n i := by
  simp only [toOriginal, AlgHom.restrictScalars_apply, pathMap, PathPresentation.lift_y]

#print axioms toOriginal_y

theorem toOriginal_parameter : toOriginal R n
    (algebraMap (Coefficient R) (Path R n) (LaurentPolynomialUniversal.parameter R))=originalParameter R n := by
  change pathMap R n (algebraMap (Coefficient R) (Path R n) _) = _
  rw [AlgHom.commutes]
  exact coefficient_parameter R n

#print axioms toOriginal_parameter

theorem toPath_x (i : Fin n) : toPath R n (originalX R n i)=x (LaurentPolynomialUniversal.parameter R) 1 i :=
  OriginalGlobalGenerators.lift_initial (S := Path R n) R (Fin 1) n (matrix n)
    (algebraMap R (Path R n)) (pathOriginals R n) (y (LaurentPolynomialUniversal.parameter R) 1)
    (path_equations R n) (path_frozen_unit R n) (Sum.inl i)

#print axioms toPath_x

theorem toPath_y (i : Fin n) : toPath R n (originalY R n i)=y (LaurentPolynomialUniversal.parameter R) 1 i :=
  OriginalGlobalGenerators.lift_mutated (S := Path R n) R (Fin 1) n (matrix n)
    (algebraMap R (Path R n)) (pathOriginals R n) (y (LaurentPolynomialUniversal.parameter R) 1)
    (path_equations R n) (path_frozen_unit R n) i

#print axioms toPath_y

theorem toPath_parameter : toPath R n (originalParameter R n)=
    algebraMap (Coefficient R) (Path R n) (LaurentPolynomialUniversal.parameter R) :=
  OriginalGlobalGenerators.lift_initial (S := Path R n) R (Fin 1) n (matrix n)
    (algebraMap R (Path R n)) (pathOriginals R n) (y (LaurentPolynomialUniversal.parameter R) 1)
    (path_equations R n) (path_frozen_unit R n) (Sum.inr 0)

#print axioms toPath_parameter

end Verification.PathOriginalZPresentation
