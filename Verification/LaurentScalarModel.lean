/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PartnerScaling
import Verification.ExchangeCharacters

/-!
# Laurent Scalar Model

Laurent exchange presentations are invariant under a change of frozen
lattice basis and a relabeling of mutable vertices. Both layers of original
and partner polynomial variables are transported by explicit maps.
-/
noncomputable section
namespace Verification.LaurentScalarModel
open MvPolynomial
open scoped BigOperators
variable (R : Type*) [CommRing R]
variable {ι τ M N : Type*} [Fintype ι] [Fintype τ] [AddCommGroup M] [AddCommGroup N]

abbrev Coefficients (M : Type*) [AddCommGroup M] := MonoidAlgebra R (Multiplicative M)

def exchange (P : ι → ι → ℤ) (f : ι → M) (c : ι → Rˣ) (i : ι) :
    MvPolynomial ι (Coefficients R M) :=
  C (algebraMap R _ (c i : R) * ExchangeCharacters.monomial (f i)) *
    (∏ r, X r ^ (P r i).toNat) + ∏ r, X r ^ (-P r i).toNat

def relations (P : ι → ι → ℤ) (f : ι → M) (c : ι → Rˣ) :
    Ideal (MvPolynomial ι (MvPolynomial ι (Coefficients R M))) :=
  PartnerScaling.relations (fun i => X i) (exchange R P f c)

local instance ambientCommRing (α L : Type*) [AddCommGroup L] :
    CommRing (MvPolynomial α (MvPolynomial α (Coefficients R L))) := inferInstance

abbrev Presentation (P : ι → ι → ℤ) (f : ι → M) (c : ι → Rˣ) :=
  MvPolynomial ι (MvPolynomial ι (Coefficients R M)) ⧸ relations R P f c

def coefficientEquiv (e : M ≃ₗ[ℤ] N) : Coefficients R M ≃ₐ[R] Coefficients R N :=
  MonoidAlgebra.domCongr R R (e.toAddEquiv.toMultiplicative)

theorem coefficientEquiv_monomial (e : M ≃ₗ[ℤ] N) (m : M) :
    coefficientEquiv R e (ExchangeCharacters.monomial m) = ExchangeCharacters.monomial (e m) := by
  exact MonoidAlgebra.domCongr_single R R (e.toAddEquiv.toMultiplicative) (Multiplicative.ofAdd m) 1

def polynomialEquiv (h : ι ≃ τ) (e : M ≃ₗ[ℤ] N) :
    MvPolynomial ι (Coefficients R M) ≃ₐ[R] MvPolynomial τ (Coefficients R N) :=
  ((renameEquiv (Coefficients R M) h).restrictScalars R).trans (mapAlgEquiv τ (coefficientEquiv R e))

omit [Fintype ι] [Fintype τ] in
theorem polynomialEquiv_X (h : ι ≃ τ) (e : M ≃ₗ[ℤ] N) (i : ι) :
    polynomialEquiv R h e (X i) = X (h i) := by
  change MvPolynomial.map (coefficientEquiv R e).toRingHom (rename h (X i)) = _
  rw [rename_X, map_X]

omit [Fintype ι] [Fintype τ] in
theorem polynomialEquiv_C (h : ι ≃ τ) (e : M ≃ₗ[ℤ] N) (q : Coefficients R M) :
    polynomialEquiv R h e (C q) = C (coefficientEquiv R e q) := by
  change MvPolynomial.map (coefficientEquiv R e).toRingHom (rename h (C q)) = _
  rw [rename_C, map_C]
  rfl

theorem product_reindex (h : ι ≃ τ) (p : ι → ℕ) :
    (∏ i, (X (h i) : MvPolynomial τ (Coefficients R N)) ^ p i) =
      ∏ j, X j ^ p (h.symm j) := by
  apply Fintype.prod_equiv h
  intro i
  simp only [Equiv.symm_apply_apply]

theorem polynomialEquiv_exchange (h : ι ≃ τ) (e : M ≃ₗ[ℤ] N)
    (P : ι → ι → ℤ) (f : ι → M) (c : ι → Rˣ) (i : ι) :
    polynomialEquiv R h e (exchange R P f c i) =
      exchange R (fun r j => P (h.symm r) (h.symm j)) (fun j => e (f (h.symm j)))
        (fun j => c (h.symm j)) (h i) := by
  simp only [exchange, map_add, map_mul, polynomialEquiv_C, map_prod, map_pow,
    polynomialEquiv_X, coefficientEquiv_monomial, AlgEquiv.commutes, Equiv.symm_apply_apply]
  rw [product_reindex, product_reindex]


def ambientEquiv (h : ι ≃ τ) (e : M ≃ₗ[ℤ] N) :
    MvPolynomial ι (MvPolynomial ι (Coefficients R M)) ≃ₐ[R]
      MvPolynomial τ (MvPolynomial τ (Coefficients R N)) :=
  ((renameEquiv (MvPolynomial ι (Coefficients R M)) h).restrictScalars R).trans
    (mapAlgEquiv τ (polynomialEquiv R h e))

theorem ambientEquiv_relation (h : ι ≃ τ) (e : M ≃ₗ[ℤ] N)
    (P : ι → ι → ℤ) (f : ι → M) (c : ι → Rˣ) (i : ι) :
    ambientEquiv R h e (C (X i) * X i - C (exchange R P f c i)) =
      C (X (h i)) * X (h i) - C (exchange R (fun r j => P (h.symm r) (h.symm j))
        (fun j => e (f (h.symm j))) (fun j => c (h.symm j)) (h i)) := by
  change MvPolynomial.map (polynomialEquiv R h e).toRingHom
    (rename h (C (X i) * X i - C (exchange R P f c i))) = _
  simp only [map_sub, map_mul, rename_C, rename_X, map_C, map_X]
  change C (polynomialEquiv R h e (X i)) * X (h i) -
    C (polynomialEquiv R h e (exchange R P f c i)) = _
  rw [polynomialEquiv_X, polynomialEquiv_exchange]

theorem map_relations (h : ι ≃ τ) (e : M ≃ₗ[ℤ] N)
    (P : ι → ι → ℤ) (f : ι → M) (c : ι → Rˣ) :
    (relations R P f c).map (ambientEquiv R h e).toRingHom =
      relations R (fun r j => P (h.symm r) (h.symm j))
        (fun j => e (f (h.symm j))) (fun j => c (h.symm j)) := by
  rw [relations, PartnerScaling.relations, Ideal.map_span, ← Set.range_comp]
  have hh : ((ambientEquiv R h e).toRingHom ∘ (fun i => C (X i) * X i - C (exchange R P f c i))) =
      (fun j => C (X j) * X j - C (exchange R (fun r j => P (h.symm r) (h.symm j))
        (fun j => e (f (h.symm j))) (fun j => c (h.symm j)) j)) ∘ h := by
    funext i
    exact ambientEquiv_relation R h e P f c i
  change Ideal.span (Set.range ((ambientEquiv R h e).toRingHom ∘
    (fun i => C (X i) * X i - C (exchange R P f c i)))) = _
  rw [hh, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  rfl

def presentationEquiv (h : ι ≃ τ) (e : M ≃ₗ[ℤ] N)
    (P : ι → ι → ℤ) (f : ι → M) (c : ι → Rˣ) :
    Presentation R P f c ≃ₐ[R]
      Presentation R (fun r j => P (h.symm r) (h.symm j))
        (fun j => e (f (h.symm j))) (fun j => c (h.symm j)) :=
  Ideal.quotientEquivAlg _ _ (ambientEquiv R h e) (map_relations R h e P f c).symm

#print axioms Coefficients
#print axioms exchange
#print axioms relations
#print axioms ambientCommRing
#print axioms Presentation
#print axioms coefficientEquiv
#print axioms coefficientEquiv_monomial
#print axioms polynomialEquiv
#print axioms polynomialEquiv_X
#print axioms polynomialEquiv_C
#print axioms product_reindex
#print axioms polynomialEquiv_exchange
#print axioms ambientEquiv
#print axioms ambientEquiv_relation
#print axioms map_relations
#print axioms presentationEquiv
end Verification.LaurentScalarModel
