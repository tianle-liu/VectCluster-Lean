/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FinsuppTorusReindex
import Verification.LaurentPolynomialUniversal

/-!
# Finite Torus Laurent

The ordered finite torus is the actual Laurent line over its tail
coordinates. The equivalence fixes the first parameter and each coefficient.
-/
noncomputable section
namespace Verification.FiniteTorusLaurent
open Verification.OriginalTorus
variable (R : Type) [CommRing R] (n : ℕ)
abbrev Base := Torus R (Fin n)
abbrev Laurent := LaurentPolynomialUniversal.Laurent (Base R n)

def coefficient : Base R n →ₐ[R] Torus R (Fin (n+1)) :=
  FinsuppTorusReindex.map R Fin.succ

theorem coefficient_coordinate (i : Fin n) :
    coefficient R n (torusCoordinate R (Fin n) i)=torusCoordinate R (Fin (n+1)) i.succ :=
  FinsuppTorusReindex.map_coordinate R Fin.succ i

def forward : Laurent R n →ₐ[R] Torus R (Fin (n+1)) :=
  LaurentPolynomialUniversal.lift (coefficient R n)
    (FinsuppTorusUniversal.unit R (Fin (n+1)) 0)

def inverseUnits : Fin (n+1) → (Laurent R n)ˣ :=
  Fin.cases (LaurentPolynomialUniversal.parameterUnit (Base R n))
    (fun i => Units.map (algebraMap (Base R n) (Laurent R n)).toMonoidHom
      (FinsuppTorusUniversal.unit R (Fin n) i))

def inverse : Torus R (Fin (n+1)) →ₐ[R] Laurent R n :=
  FinsuppTorusUniversal.lift R (Fin (n+1)) (inverseUnits R n)

theorem forward_parameter : forward R n (LaurentPolynomialUniversal.parameter (Base R n))=
    torusCoordinate R (Fin (n+1)) 0 := LaurentPolynomialUniversal.lift_parameter _ _

theorem forward_coefficient (a : Base R n) : forward R n (algebraMap (Base R n) (Laurent R n) a)=
    coefficient R n a := LaurentPolynomialUniversal.lift_coefficient _ _ _

theorem inverse_coordinate (i : Fin (n+1)) : inverse R n (torusCoordinate R (Fin (n+1)) i)=
    (inverseUnits R n i : Laurent R n) := FinsuppTorusUniversal.lift_coordinate _ _ _ _

theorem inverse_coefficient : (inverse R n).comp (coefficient R n)=
    LaurentBasepoint.coefficient R (Base R n) := by
  apply FinsuppTorusUniversal.hom_ext
  intro i
  change inverse R n (coefficient R n (torusCoordinate R (Fin n) i))=_
  rw [coefficient_coordinate,inverse_coordinate]
  rfl

theorem forward_inverse : (forward R n).comp (inverse R n)=AlgHom.id R _ := by
  apply FinsuppTorusUniversal.hom_ext
  intro i
  change forward R n (inverse R n (torusCoordinate R (Fin (n+1)) i))=_
  rw [inverse_coordinate]
  refine Fin.cases ?_ (fun k => ?_) i
  · change forward R n (LaurentPolynomialUniversal.parameterUnit (Base R n) : Laurent R n)=_
    rw [LaurentPolynomialUniversal.parameterUnit_val,forward_parameter]
    rfl
  · change forward R n (algebraMap (Base R n) (Laurent R n) (torusCoordinate R (Fin n) k))=_
    rw [forward_coefficient,coefficient_coordinate]
    rfl

theorem inverse_forward : (inverse R n).comp (forward R n)=AlgHom.id R _ := by
  apply LaurentPolynomialUniversal.hom_ext
  · intro a
    change inverse R n (forward R n (algebraMap (Base R n) (Laurent R n) a))=_
    rw [forward_coefficient]
    exact AlgHom.congr_fun (inverse_coefficient R n) a
  · change inverse R n (forward R n (LaurentPolynomialUniversal.parameter (Base R n)))=_
    rw [forward_parameter,inverse_coordinate]
    exact LaurentPolynomialUniversal.parameterUnit_val

def equiv : Laurent R n ≃ₐ[R] Torus R (Fin (n+1)) :=
  AlgEquiv.ofAlgHom (forward R n) (inverse R n) (forward_inverse R n) (inverse_forward R n)

#print axioms Base
#print axioms Laurent
#print axioms coefficient
#print axioms coefficient_coordinate
#print axioms forward
#print axioms inverseUnits
#print axioms inverse
#print axioms forward_parameter
#print axioms forward_coefficient
#print axioms inverse_coordinate
#print axioms inverse_coefficient
#print axioms forward_inverse
#print axioms inverse_forward
#print axioms equiv
end Verification.FiniteTorusLaurent
