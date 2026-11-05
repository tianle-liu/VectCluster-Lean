/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalZPresentation

/-!
# Path Original Z Equivalence

The complete R-algebra equivalence from the literal Laurent-coefficient
path Z to its actual one-frozen-coordinate global exchange ring.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
namespace Verification.PathOriginalZEquivalence
open Verification.PathOriginalZPresentation Verification.PathPresentation
open Verification.FrozenAcyclicCover
variable (R : Type) [CommRing R] (n : ℕ)

theorem toPath_coefficient (a : Coefficient R) :
    toPath R n (coefficientMap R n a)=algebraMap (Coefficient R) (Path R n) a := by
  have hh : (toPath R n).comp (coefficientMap R n) = IsScalarTower.toAlgHom R (Coefficient R) (Path R n) := by
    apply LaurentPolynomialUniversal.hom_ext
    · intro r
      exact ((toPath R n).comp (coefficientMap R n)).commutes r |>.trans
        ((IsScalarTower.toAlgHom R (Coefficient R) (Path R n)).commutes r).symm
    · change toPath R n (coefficientMap R n (LaurentPolynomialUniversal.parameter R)) = _
      rw [coefficient_parameter,toPath_parameter]
      rfl
  exact AlgHom.congr_fun hh a

def toPathOverCoefficient : Original R n →ₐ[Coefficient R] Path R n where
  __ := (toPath R n).toRingHom
  commutes' := toPath_coefficient R n

theorem toPath_toOriginal : (toPath R n).comp (toOriginal R n)=AlgHom.id R _ := by
  have hh : (toPathOverCoefficient R n).comp (pathMap R n)=AlgHom.id (Coefficient R) _ := by
    apply PathPresentation.hom_ext
    · intro i
      change toPath R n (toOriginal R n (x (LaurentPolynomialUniversal.parameter R) 1 i))=_
      rw [toOriginal_x,toPath_x]
      rfl
    · intro i
      change toPath R n (toOriginal R n (y (LaurentPolynomialUniversal.parameter R) 1 i))=_
      rw [toOriginal_y,toPath_y]
      rfl
  apply AlgHom.coe_ringHom_injective
  exact congrArg AlgHom.toRingHom hh

theorem toOriginal_toPath : (toOriginal R n).comp (toPath R n)=AlgHom.id R _ := by
  apply AlgHom.coe_ringHom_injective
  apply OriginalGlobalGenerators.hom_ext R (Fin 1) n (matrix n)
  · intro r
    change toOriginal R n (toPath R n (algebraMap R _ r))=algebraMap R _ r
    rw [AlgHom.commutes,AlgHom.commutes]
  · intro a
    cases a with
    | inl i =>
      change toOriginal R n (toPath R n (originalX R n i))=originalX R n i
      rw [toPath_x,toOriginal_x]
    | inr k =>
      have hk : k=0 := Subsingleton.elim _ _
      subst k
      change toOriginal R n (toPath R n (originalParameter R n))=originalParameter R n
      rw [toPath_parameter,toOriginal_parameter]
  · intro i
    change toOriginal R n (toPath R n (originalY R n i))=originalY R n i
    rw [toPath_y,toOriginal_y]

def equiv : Path R n ≃ₐ[R] Original R n :=
  AlgEquiv.ofAlgHom (toOriginal R n) (toPath R n) (toOriginal_toPath R n) (toPath_toOriginal R n)

theorem equiv_x (i : Fin n) : equiv R n (x (LaurentPolynomialUniversal.parameter R) 1 i)=
    initial R (Fin 1) n (matrix n) (Sum.inl i) := toOriginal_x R n i

theorem equiv_y (i : Fin n) : equiv R n (y (LaurentPolynomialUniversal.parameter R) 1 i)=
    mutated R (Fin 1) n (matrix n) i := toOriginal_y R n i

theorem equiv_parameter : equiv R n
    (algebraMap (Coefficient R) (Path R n) (LaurentPolynomialUniversal.parameter R))=
      initial R (Fin 1) n (matrix n) (Sum.inr 0) := toOriginal_parameter R n

#print axioms toPath_coefficient
#print axioms toPathOverCoefficient
#print axioms toPath_toOriginal
#print axioms toOriginal_toPath
#print axioms equiv
#print axioms equiv_x
#print axioms equiv_y
#print axioms equiv_parameter
end Verification.PathOriginalZEquivalence
