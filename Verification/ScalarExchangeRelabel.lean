/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExchangeRelabel

/-!
# Scalar Exchange Relabel

Relabel the actual two-scalar exchange ideal and both coordinate
families. Coefficients are transported with their own exchange columns.
-/
noncomputable section
namespace Verification.ScalarExchangeRelabel
open MvPolynomial
open Verification.ExchangeRelabel (polynomialEquiv polynomialEquiv_X polynomialEquiv_C)
open scoped BigOperators
variable (R : Type*) [CommRing R]
variable {ρ σ ρ' σ' : Type*} [Fintype ρ] [Fintype ρ']

def powerSum (p : ρ → ℤ) (a b : Rˣ) : MvPolynomial ρ R :=
  C (a : R) * (∏ r, X r ^ (p r).toNat) + C (b : R) * ∏ r, X r ^ (-p r).toNat

theorem rename_powerSum (e : ρ ≃ ρ') (p : ρ → ℤ) (p' : ρ' → ℤ) (a b : Rˣ)
    (hp : ∀ r, p' (e r) = p r) : rename e (powerSum R p a b) = powerSum R p' a b := by
  simp only [powerSum, map_add, map_mul, rename_C, map_prod, map_pow, rename_X]
  have hpos := Fintype.prod_equiv e (fun r => (X (e r) : MvPolynomial ρ' R) ^ (p r).toNat)
    (fun r => X r ^ (p' r).toNat) (fun r => by simp only [hp r])
  have hneg := Fintype.prod_equiv e (fun r => (X (e r) : MvPolynomial ρ' R) ^ (-p r).toNat)
    (fun r => X r ^ (-p' r).toNat) (fun r => by simp only [hp r])
  rw [hpos,hneg]

def relation (j : σ → ρ) (B : ρ → σ → ℤ) (a b : σ → Rˣ) (v : σ) :
    MvPolynomial σ (MvPolynomial ρ R) :=
  C (X (j v)) * X v - C (powerSum R (fun r => B r v) (a v) (b v))

def relations (j : σ → ρ) (B : ρ → σ → ℤ) (a b : σ → Rˣ) :
    Ideal (MvPolynomial σ (MvPolynomial ρ R)) := Ideal.span (Set.range (relation R j B a b))

theorem polynomialEquiv_relation (e : ρ ≃ ρ') (d : σ ≃ σ')
    (j : σ → ρ) (j' : σ' → ρ') (B : ρ → σ → ℤ) (B' : ρ' → σ' → ℤ) (a b : σ → Rˣ)
    (hj : ∀ v, j' (d v) = e (j v)) (hB : ∀ r v, B' (e r) (d v) = B r v) (v : σ) :
    polynomialEquiv R e d (relation R j B a b v) =
      relation R j' B' (fun w => a (d.symm w)) (fun w => b (d.symm w)) (d v) := by
  simp only [relation, map_sub, map_mul, polynomialEquiv_C, polynomialEquiv_X, rename_X,
    hj v, Equiv.symm_apply_apply,
    rename_powerSum R e (fun r => B r v) (fun r => B' r (d v)) (a v) (b v) (fun r => hB r v)]

theorem map_relations (e : ρ ≃ ρ') (d : σ ≃ σ')
    (j : σ → ρ) (j' : σ' → ρ') (B : ρ → σ → ℤ) (B' : ρ' → σ' → ℤ) (a b : σ → Rˣ)
    (hj : ∀ v, j' (d v) = e (j v)) (hB : ∀ r v, B' (e r) (d v) = B r v) :
    (relations R j B a b).map (polynomialEquiv R e d).toRingHom =
      relations R j' B' (fun w => a (d.symm w)) (fun w => b (d.symm w)) := by
  rw [relations, Ideal.map_span, relations]
  congr 1
  ext p
  constructor
  · rintro ⟨_,⟨v,rfl⟩,rfl⟩
    exact ⟨d v,(polynomialEquiv_relation R e d j j' B B' a b hj hB v).symm⟩
  · rintro ⟨v,rfl⟩
    refine ⟨relation R j B a b (d.symm v),Set.mem_range_self _,?_⟩
    simpa only [d.apply_symm_apply] using polynomialEquiv_relation R e d j j' B B' a b hj hB (d.symm v)

def quotientEquiv (e : ρ ≃ ρ') (d : σ ≃ σ')
    (j : σ → ρ) (j' : σ' → ρ') (B : ρ → σ → ℤ) (B' : ρ' → σ' → ℤ) (a b : σ → Rˣ)
    (hj : ∀ v, j' (d v) = e (j v)) (hB : ∀ r v, B' (e r) (d v) = B r v) :
    (MvPolynomial σ (MvPolynomial ρ R) ⧸ relations R j B a b) ≃ₐ[R]
      (MvPolynomial σ' (MvPolynomial ρ' R) ⧸ relations R j' B' (fun w => a (d.symm w)) (fun w => b (d.symm w))) :=
  Ideal.quotientEquivAlg _ _ (polynomialEquiv R e d) (map_relations R e d j j' B B' a b hj hB).symm

theorem quotientEquiv_original (e : ρ ≃ ρ') (d : σ ≃ σ')
    (j : σ → ρ) (j' : σ' → ρ') (B : ρ → σ → ℤ) (B' : ρ' → σ' → ℤ) (a b : σ → Rˣ)
    (hj : ∀ v, j' (d v) = e (j v)) (hB : ∀ r v, B' (e r) (d v) = B r v) (q : ρ) :
    quotientEquiv R e d j j' B B' a b hj hB (Ideal.Quotient.mk _ (C (X q))) =
      Ideal.Quotient.mk (relations R j' B' (fun w => a (d.symm w)) (fun w => b (d.symm w)))
        (C (X (e q))) := by
  change Ideal.Quotient.mk _ (polynomialEquiv R e d (C (X q))) = _
  rw [polynomialEquiv_C,rename_X]

#print axioms powerSum
#print axioms rename_powerSum
#print axioms relation
#print axioms relations
#print axioms polynomialEquiv_relation
#print axioms map_relations
#print axioms quotientEquiv
#print axioms quotientEquiv_original
end Verification.ScalarExchangeRelabel
