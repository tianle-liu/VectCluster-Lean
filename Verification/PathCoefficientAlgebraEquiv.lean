/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathTower
import Verification.NestedExchangeCoordinateEquiv

/-!
# Path Coefficient Algebra Equiv

A genuine coefficient-algebra isomorphism transports the literal path
quotient and both endpoint constants.
-/
noncomputable section
namespace Verification.PathCoefficientAlgebraEquiv
open MvPolynomial Verification.PathPresentation
variable (R : Type*) [CommRing R] {S T : Type*} [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] (e : S ≃ₐ[R] T) (n : ℕ) (a b : S)

theorem relation_map (i : Fin n) :
    mapAlgEquiv (Fin n ⊕ Fin n) e (relation a b i)=relation (e a) (e b) i := by
  simp only [relation,map_sub,map_mul,boundary_map (mapAlgEquiv (Fin n ⊕ Fin n) e),mapAlgEquiv_apply,map_X,map_C]
  rfl

theorem relations_map : (relations n a b).map (mapAlgEquiv (Fin n ⊕ Fin n) e).toRingHom=
    relations n (e a) (e b) := by
  rw [relations,Ideal.map_span,← Set.range_comp]
  change Ideal.span (Set.range (fun i=>mapAlgEquiv (Fin n ⊕ Fin n) e (relation a b i)))=_
  simp only [relation_map]
  rfl

def equiv : PathAlgebra n a b ≃ₐ[R] PathAlgebra n (e a) (e b) :=
  Ideal.quotientEquivAlg _ _ (mapAlgEquiv (Fin n ⊕ Fin n) e) (relations_map R e n a b).symm

def endpointEquiv (a' b' : T) (ha : e a=a') (hb : e b=b') :
    PathAlgebra n a b ≃ₐ[R] PathAlgebra n a' b' :=
  (equiv R e n a b).trans
    (Ideal.quotientEquivAlgOfEq R (congrArg₂ (relations n) ha hb))

#print axioms relation_map
#print axioms relations_map
#print axioms equiv
#print axioms endpointEquiv
end Verification.PathCoefficientAlgebraEquiv
