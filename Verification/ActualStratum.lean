/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocallyClosedPresentation
import Verification.CoordinateTransport
import Mathlib.Algebra.BigOperators.Fin

/-!
# Actual Stratum

The AS affine-times-torus calculation for an actual locally closed locus
of the globally presented exchange ring. All original coordinates occur in
the two exchange monomials. The vanishing block of an independent set is
used to delete its zero rows; all other partners are eliminated by the
previous explicit quotient maps. Extra frozen coordinates need no partners.
-/
namespace Verification.ActualStratum
open MvPolynomial Verification.StratumPresentation
open Verification.CoordinateTransport Verification.LocallyClosedPresentation
open scoped BigOperators
variable (R ι κ τ : Type*) [CommRing R] [Fintype ι] [Fintype κ]

abbrev OriginalPolynomial := MvPolynomial (ι ⊕ κ) R

noncomputable def initialPolynomial (j : τ → κ) : (ι ⊕ τ) → OriginalPolynomial R ι κ :=
  Sum.elim (fun i => X (Sum.inl i)) (fun t => X (Sum.inr (j t)))

noncomputable def exchangePolynomial (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (v : ι ⊕ τ) : OriginalPolynomial R ι κ :=
  (∏ a, X a ^ (B a v).toNat) + ∏ a, X a ^ (-B a v).toNat

noncomputable def originalBaseMap : OriginalPolynomial R ι κ →+* OriginalStratum R ι κ :=
  baseMap (zeroCoordinateIdeal R ι κ) (fun k : κ => X (Sum.inr k))

omit [Fintype ι] [Fintype κ] in
theorem originalBaseMap_X (a : ι ⊕ κ) :
    originalBaseMap R ι κ (X a) = originalCoordinate R ι κ a := rfl

omit [Fintype ι] [Fintype κ] in
theorem initialPolynomial_map (j : τ → κ) :
    (fun v => originalBaseMap R ι κ (initialPolynomial R ι κ τ j v)) =
      initialCoordinates R ι κ j := by
  funext v
  cases v <;> rfl

theorem exchangePolynomial_map_zero_column
    (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (i : ι)
    (hB : ∀ a : ι, B (Sum.inl a) (Sum.inl i) = 0) :
    originalBaseMap R ι κ (exchangePolynomial R ι κ τ B (Sum.inl i)) =
      originalExchange R ι κ Finset.univ (fun a => B (Sum.inr a) (Sum.inl i)) := by
  simp only [exchangePolynomial, map_add, map_prod, map_pow, originalBaseMap_X,
    Fintype.prod_sum_type, hB, Int.toNat_zero, neg_zero, pow_zero, Finset.prod_const_one,
    one_mul, originalExchange]

noncomputable abbrev GlobalZeroStratum (j : τ → κ)
    (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) :=
  LocallyClosedRing (zeroCoordinateIdeal R ι κ)
    (initialPolynomial R ι κ τ j) (exchangePolynomial R ι κ τ B)
    (fun k : κ => X (Sum.inr k))

variable {P : Type*} [AddCommGroup P]

/-- The actual original zero stratum is affine space over its primitive
character fiber. Saturation and independence belong to the original column
map; no split torus or stratum identification is assumed. -/
theorem global_zero_stratum
    (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0)
    (f : P →ₗ[ℤ] (κ →₀ ℤ)) (basis : Basis ι ℤ P)
    (hf : ∀ i, f (basis i) = Verification.ExchangeCharacters.column Finset.univ
      (fun a => B (Sum.inr a) (Sum.inl i)) (fun k => Finsupp.single k 1))
    (hinj : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    Nonempty (GlobalZeroStratum R ι κ τ j B ≃+*
      MvPolynomial ι (MonoidAlgebra R (Multiplicative ((κ →₀ ℤ) ⧸ LinearMap.range f)))) := by
  let other : τ → OriginalStratum R ι κ :=
    fun t => originalBaseMap R ι κ (exchangePolynomial R ι κ τ B (Sum.inr t))
  have hg : (fun v => originalBaseMap R ι κ (exchangePolynomial R ι κ τ B v)) =
      Sum.elim (fun i => originalExchange R ι κ Finset.univ
        (fun a => B (Sum.inr a) (Sum.inl i))) other := by
    funext v
    cases v with
    | inl i => exact exchangePolynomial_map_zero_column R ι κ τ B i (fun a => hB a i)
    | inr t => rfl
  have e := locallyClosedEquiv (zeroCoordinateIdeal R ι κ)
    (initialPolynomial R ι κ τ j) (exchangePolynomial R ι κ τ B)
    (fun k : κ => (X (Sum.inr k) : OriginalPolynomial R ι κ))
  change GlobalZeroStratum R ι κ τ j B ≃+*
    (MvPolynomial (ι ⊕ τ) (OriginalStratum R ι κ) ⧸ exchangeIdeal
      (fun v => originalBaseMap R ι κ (initialPolynomial R ι κ τ j v))
      (fun v => originalBaseMap R ι κ (exchangePolynomial R ι κ τ B v))) at e
  rw [initialPolynomial_map, hg] at e
  obtain ⟨q⟩ := original_primitive_stratum R ι κ Finset.univ
    (fun a i => B (Sum.inr a) (Sum.inl i)) f basis hf hinj hs j other
  exact ⟨e.trans q⟩

#print axioms OriginalPolynomial
#print axioms initialPolynomial
#print axioms exchangePolynomial
#print axioms originalBaseMap
#print axioms originalBaseMap_X
#print axioms initialPolynomial_map
#print axioms exchangePolynomial_map_zero_column
#print axioms GlobalZeroStratum
#print axioms global_zero_stratum
end Verification.ActualStratum
