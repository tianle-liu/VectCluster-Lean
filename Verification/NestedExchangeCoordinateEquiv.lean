/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.NestedExchangeUniversal

/-!
# Nested Exchange Coordinate Equiv

Actual exchange quotients transport along a coefficient-algebra isomorphism
and a bijection of mutable coordinates, preserving both original and partner variables.
-/
noncomputable section
namespace Verification.NestedExchangeCoordinateEquiv
open MvPolynomial
variable (R : Type*) [CommRing R] {S T : Type*} [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] {ι τ : Type*}
variable (h : ι ≃ τ) (e : S ≃ₐ[R] T)

def polynomial : MvPolynomial ι S ≃ₐ[R] MvPolynomial τ T :=
  ((renameEquiv S h).restrictScalars R).trans (mapAlgEquiv τ e)

theorem polynomial_X (i : ι) : polynomial R h e (X i)=X (h i) := by
  change MvPolynomial.map e.toRingHom (rename h (X i))=_
  rw [rename_X,map_X]

theorem polynomial_C (s : S) : polynomial R h e (C s)=C (e s) := by
  change MvPolynomial.map e.toRingHom (rename h (C s))=_
  rw [rename_C,map_C]
  rfl

def ambient : MvPolynomial ι (MvPolynomial ι S) ≃ₐ[R]
    MvPolynomial τ (MvPolynomial τ T) :=
  ((renameEquiv (MvPolynomial ι S) h).restrictScalars R).trans
    (mapAlgEquiv τ (polynomial R h e))

def transported (p : ι → MvPolynomial ι S) (j : τ) : MvPolynomial τ T :=
  polynomial R h e (p (h.symm j))

theorem relation (p : ι → MvPolynomial ι S) (i : ι) :
    ambient R h e (PartnerScaling.relation (fun i=>X i) p i)=
      PartnerScaling.relation (fun j=>X j) (transported R h e p) (h i) := by
  change MvPolynomial.map (polynomial R h e).toRingHom
    (rename h (C (X i)*X i-C (p i)))=_
  simp only [map_sub,map_mul,rename_C,rename_X,map_C,map_X]
  change C (polynomial R h e (X i))*X (h i)-C (polynomial R h e (p i))=_
  rw [polynomial_X]
  simp only [PartnerScaling.relation,transported,Equiv.symm_apply_apply]

theorem relations (p : ι → MvPolynomial ι S) :
    (PartnerScaling.relations (fun i=>X i) p).map (ambient R h e).toRingHom=
      PartnerScaling.relations (fun j=>X j) (transported R h e p) := by
  rw [PartnerScaling.relations,Ideal.map_span,← Set.range_comp]
  have he : (ambient R h e).toRingHom ∘ PartnerScaling.relation (fun i=>X i) p=
      PartnerScaling.relation (fun j=>X j) (transported R h e p) ∘ h := by
    funext i
    exact relation R h e p i
  rw [he,Set.range_comp,Equiv.range_eq_univ,Set.image_univ]
  rfl

def equiv (p : ι → MvPolynomial ι S) : NestedExchangeUniversal.Ring S p ≃ₐ[R]
    NestedExchangeUniversal.Ring T (transported R h e p) :=
  Ideal.quotientEquivAlg _ _ (ambient R h e) (relations R h e p).symm

theorem equiv_x (p : ι → MvPolynomial ι S) (i : ι) :
    equiv R h e p (NestedExchangeUniversal.x S p i)=
      NestedExchangeUniversal.x T (transported R h e p) (h i) := by
  change Ideal.Quotient.mk _ (ambient R h e (C (X i)))=_
  change Ideal.Quotient.mk _ (MvPolynomial.map (polynomial R h e).toRingHom (rename h (C (X i))))=_
  rw [rename_C,map_C]
  change Ideal.Quotient.mk _ (C (polynomial R h e (X i)))=_
  rw [polynomial_X]
  rfl

theorem equiv_y (p : ι → MvPolynomial ι S) (i : ι) :
    equiv R h e p (NestedExchangeUniversal.y S p i)=
      NestedExchangeUniversal.y T (transported R h e p) (h i) := by
  change Ideal.Quotient.mk _ (MvPolynomial.map (polynomial R h e).toRingHom (rename h (X i)))=_
  rw [rename_X,map_X]
  rfl

#print axioms polynomial
#print axioms polynomial_X
#print axioms polynomial_C
#print axioms ambient
#print axioms transported
#print axioms relation
#print axioms relations
#print axioms equiv
#print axioms equiv_x
#print axioms equiv_y
end Verification.NestedExchangeCoordinateEquiv
