/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StratumPresentation
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Exchange Relabel

Simultaneous relabeling of original coordinates and exchange partners.
The all-row exchange ideal is transported literally, including both signed
monomials. This is the algebraic input for selecting an arbitrary zero set.
-/
noncomputable section
namespace Verification.ExchangeRelabel
open MvPolynomial
open scoped BigOperators
variable (R : Type*) [CommRing R]
variable {ρ σ ρ' σ' : Type*} [Fintype ρ] [Fintype ρ']

def polynomialEquiv (e : ρ ≃ ρ') (d : σ ≃ σ') :
    MvPolynomial σ (MvPolynomial ρ R) ≃ₐ[R] MvPolynomial σ' (MvPolynomial ρ' R) :=
  (mapAlgEquiv σ (renameEquiv R e)).trans ((renameEquiv (MvPolynomial ρ' R) d).restrictScalars R)

omit [Fintype ρ] [Fintype ρ'] in
theorem polynomialEquiv_X (e : ρ ≃ ρ') (d : σ ≃ σ') (v : σ) :
    polynomialEquiv R e d (X v) = X (d v) := by
  change rename d (MvPolynomial.map (renameEquiv R e).toRingHom (X v)) = _
  rw [map_X, rename_X]

omit [Fintype ρ] [Fintype ρ'] in
theorem polynomialEquiv_C (e : ρ ≃ ρ') (d : σ ≃ σ') (p : MvPolynomial ρ R) :
    polynomialEquiv R e d (C p) = C (rename e p) := by
  change rename d (MvPolynomial.map (renameEquiv R e).toRingHom (C p)) = _
  rw [map_C, rename_C]
  rfl

def powerSum (b : ρ → ℤ) : MvPolynomial ρ R :=
  (∏ a, X a ^ (b a).toNat) + ∏ a, X a ^ (-b a).toNat

theorem rename_powerSum (e : ρ ≃ ρ') (b : ρ → ℤ) (b' : ρ' → ℤ)
    (hb : ∀ a, b' (e a) = b a) : rename e (powerSum R b) = powerSum R b' := by
  simp only [powerSum, map_add, map_prod, map_pow, rename_X]
  congr 1
  · exact Fintype.prod_equiv e _ _ (fun a => by rw [hb a])
  · exact Fintype.prod_equiv e _ _ (fun a => by rw [hb a])

def relation (j : σ → ρ) (B : ρ → σ → ℤ) (v : σ) : MvPolynomial σ (MvPolynomial ρ R) :=
  C (X (j v)) * X v - C (powerSum R (fun a => B a v))

def relations (j : σ → ρ) (B : ρ → σ → ℤ) : Ideal (MvPolynomial σ (MvPolynomial ρ R)) :=
  Ideal.span (Set.range (relation R j B))

theorem polynomialEquiv_relation (e : ρ ≃ ρ') (d : σ ≃ σ')
    (j : σ → ρ) (j' : σ' → ρ') (B : ρ → σ → ℤ) (B' : ρ' → σ' → ℤ)
    (hj : ∀ v, j' (d v) = e (j v)) (hB : ∀ a v, B' (e a) (d v) = B a v) (v : σ) :
    polynomialEquiv R e d (relation R j B v) = relation R j' B' (d v) := by
  simp only [relation, map_sub, map_mul, polynomialEquiv_C, polynomialEquiv_X, rename_X,
    hj v, rename_powerSum R e (fun a => B a v) (fun a => B' a (d v)) (fun a => hB a v)]

theorem map_relations (e : ρ ≃ ρ') (d : σ ≃ σ')
    (j : σ → ρ) (j' : σ' → ρ') (B : ρ → σ → ℤ) (B' : ρ' → σ' → ℤ)
    (hj : ∀ v, j' (d v) = e (j v)) (hB : ∀ a v, B' (e a) (d v) = B a v) :
    (relations R j B).map (polynomialEquiv R e d).toRingHom = relations R j' B' := by
  rw [relations, Ideal.map_span, relations]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨d v, (polynomialEquiv_relation R e d j j' B B' hj hB v).symm⟩
  · rintro ⟨v, rfl⟩
    refine ⟨relation R j B (d.symm v), Set.mem_range_self _, ?_⟩
    simpa only [d.apply_symm_apply] using polynomialEquiv_relation R e d j j' B B' hj hB (d.symm v)

def quotientEquiv (e : ρ ≃ ρ') (d : σ ≃ σ')
    (j : σ → ρ) (j' : σ' → ρ') (B : ρ → σ → ℤ) (B' : ρ' → σ' → ℤ)
    (hj : ∀ v, j' (d v) = e (j v)) (hB : ∀ a v, B' (e a) (d v) = B a v) :
    (MvPolynomial σ (MvPolynomial ρ R) ⧸ relations R j B) ≃ₐ[R]
      (MvPolynomial σ' (MvPolynomial ρ' R) ⧸ relations R j' B') :=
  Ideal.quotientEquivAlg _ _ (polynomialEquiv R e d) (map_relations R e d j j' B B' hj hB).symm

def original (j : σ → ρ) (B : ρ → σ → ℤ) (a : ρ) :
    MvPolynomial σ (MvPolynomial ρ R) ⧸ relations R j B := Ideal.Quotient.mk _ (C (X a))

theorem quotientEquiv_original (e : ρ ≃ ρ') (d : σ ≃ σ')
    (j : σ → ρ) (j' : σ' → ρ') (B : ρ → σ → ℤ) (B' : ρ' → σ' → ℤ)
    (hj : ∀ v, j' (d v) = e (j v)) (hB : ∀ a v, B' (e a) (d v) = B a v) (a : ρ) :
    quotientEquiv R e d j j' B B' hj hB (original R j B a) = original R j' B' (e a) := by
  change Ideal.Quotient.mk _ (polynomialEquiv R e d (C (X a))) = _
  rw [polynomialEquiv_C, rename_X]
  rfl

def coordinateMonoid {γ : Type*} (j : σ → ρ) (B : ρ → σ → ℤ) (v : γ → ρ) :
    Submonoid (MvPolynomial σ (MvPolynomial ρ R) ⧸ relations R j B) :=
  Submonoid.closure (Set.range (fun c => original R j B (v c)))

abbrev Localized {γ : Type*} (j : σ → ρ) (B : ρ → σ → ℤ) (v : γ → ρ) :=
  Localization (M := MvPolynomial σ (MvPolynomial ρ R) ⧸ relations R j B) (coordinateMonoid R j B v)

theorem map_coordinateMonoid {γ : Type*} (e : ρ ≃ ρ') (d : σ ≃ σ')
    (j : σ → ρ) (j' : σ' → ρ') (B : ρ → σ → ℤ) (B' : ρ' → σ' → ℤ)
    (hj : ∀ v, j' (d v) = e (j v)) (hB : ∀ a v, B' (e a) (d v) = B a v)
    (v : γ → ρ) (v' : γ → ρ') (hv : ∀ c, e (v c) = v' c) :
    (coordinateMonoid R j B v).map (quotientEquiv R e d j j' B B' hj hB).toMonoidHom =
      coordinateMonoid R j' B' v' := by
  rw [coordinateMonoid, MonoidHom.map_mclosure, ← Set.range_comp, coordinateMonoid]
  apply congrArg Submonoid.closure
  apply congrArg Set.range
  funext c
  exact (quotientEquiv_original R e d j j' B B' hj hB (v c)).trans (congrArg _ (hv c))

def localizedRingEquiv {γ : Type*} (e : ρ ≃ ρ') (d : σ ≃ σ')
    (j : σ → ρ) (j' : σ' → ρ') (B : ρ → σ → ℤ) (B' : ρ' → σ' → ℤ)
    (hj : ∀ v, j' (d v) = e (j v)) (hB : ∀ a v, B' (e a) (d v) = B a v)
    (v : γ → ρ) (v' : γ → ρ') (hv : ∀ c, e (v c) = v' c) :
    Localized R j B v ≃+* Localized R j' B' v' :=
  IsLocalization.ringEquivOfRingEquiv (Localized R j B v)
    (Localized R j' B' v') (quotientEquiv R e d j j' B B' hj hB).toRingEquiv
    (map_coordinateMonoid R e d j j' B B' hj hB v v' hv)

def localizedEquiv {γ : Type*} (e : ρ ≃ ρ') (d : σ ≃ σ')
    (j : σ → ρ) (j' : σ' → ρ') (B : ρ → σ → ℤ) (B' : ρ' → σ' → ℤ)
    (hj : ∀ v, j' (d v) = e (j v)) (hB : ∀ a v, B' (e a) (d v) = B a v)
    (v : γ → ρ) (v' : γ → ρ') (hv : ∀ c, e (v c) = v' c) :
    Localized R j B v ≃ₐ[R] Localized R j' B' v' :=
  IsLocalization.algEquivOfAlgEquiv (Localized R j B v)
    (Localized R j' B' v') (quotientEquiv R e d j j' B B' hj hB)
    (map_coordinateMonoid R e d j j' B B' hj hB v v' hv)

#print axioms polynomialEquiv
#print axioms polynomialEquiv_X
#print axioms polynomialEquiv_C
#print axioms powerSum
#print axioms rename_powerSum
#print axioms relation
#print axioms relations
#print axioms polynomialEquiv_relation
#print axioms map_relations
#print axioms quotientEquiv
#print axioms original
#print axioms quotientEquiv_original
#print axioms coordinateMonoid
#print axioms Localized
#print axioms map_coordinateMonoid
#print axioms localizedRingEquiv
#print axioms localizedEquiv
end Verification.ExchangeRelabel
