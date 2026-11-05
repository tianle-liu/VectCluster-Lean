/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalTorus
import Verification.ExchangeCharacters

/-!
# Coordinate Transport

Transporting the original localized exchange presentation to its actual
Laurent characters, retaining the original coordinates under the isomorphism.
Frozen original coordinates are allowed: the complementary mutable partners
are indexed separately from all remaining original coordinates.
-/
namespace Verification.CoordinateTransport
open MvPolynomial Verification.StratumPresentation
open scoped BigOperators
variable {R S ι τ : Type*} [CommRing R] [CommRing S]

theorem map_exchangeIdeal (e : R ≃+* S) (x f : (ι ⊕ τ) → R) :
    (exchangeIdeal x f).map (MvPolynomial.mapEquiv (ι ⊕ τ) e).toRingHom =
      exchangeIdeal (fun v => e (x v)) (fun v => e (f v)) := by
  rw [exchangeIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext v
  simp [Function.comp_def, exchangeRelation]

noncomputable def quotientTransport (e : R ≃+* S) (x f : (ι ⊕ τ) → R) :
    (MvPolynomial (ι ⊕ τ) R ⧸ exchangeIdeal x f) ≃+*
      (MvPolynomial (ι ⊕ τ) S ⧸
        exchangeIdeal (fun v => e (x v)) (fun v => e (f v))) :=
  Ideal.quotientEquiv _ _ (MvPolynomial.mapEquiv _ e) (map_exchangeIdeal e x f).symm

open Verification.OriginalTorus Verification.ExchangeCharacters
variable (R ι κ : Type*) [CommRing R]

noncomputable def originalExchange (s : Finset κ) (b : κ → ℤ) : OriginalStratum R ι κ :=
  (∏ a ∈ s, originalCoordinate R ι κ (Sum.inr a) ^ (b a).toNat) +
    ∏ a ∈ s, originalCoordinate R ι κ (Sum.inr a) ^ (-b a).toNat

theorem originalTorusEquiv_coordinate (k : κ) :
    originalTorusEquiv R ι κ (originalCoordinate R ι κ (Sum.inr k)) =
      Verification.ExchangeCharacters.monomial (Finsupp.single k 1 : κ →₀ ℤ) :=
  toTorus_coordinate R ι κ k

theorem originalTorusEquiv_exchange (s : Finset κ) (b : κ → ℤ) :
    originalTorusEquiv R ι κ (originalExchange R ι κ s b) =
      exchange (R := R) s b (fun k => Finsupp.single k 1) := by
  simp only [originalExchange, exchange, map_add, map_prod, map_pow,
    originalTorusEquiv_coordinate]

variable {τ : Type*}

/-- The zero coordinates and complementary mutable coordinates in the actual base.
The map j leaves any extra (frozen) invertible coordinates without partners. -/
noncomputable def initialCoordinates (j : τ → κ) : (ι ⊕ τ) → OriginalStratum R ι κ :=
  Sum.elim (fun i => originalCoordinate R ι κ (Sum.inl i))
    (fun t => originalCoordinate R ι κ (Sum.inr (j t)))

theorem initialCoordinates_zero (j : τ → κ) (i : ι) :
    initialCoordinates R ι κ j (Sum.inl i) = 0 :=
  originalCoordinate_zero R ι κ i

theorem initialCoordinates_unit (j : τ → κ) (t : τ) :
    initialCoordinates R ι κ j (Sum.inr t) = (coordinateUnit R ι κ (j t) : OriginalStratum R ι κ) :=
  (coordinateUnit_val R ι κ (j t)).symm

variable {P : Type*} [AddCommGroup P] [Fintype κ]

/-- The primitive zero-stratum computation on the original localized base,
with no assumed Laurent identification or character-equation identification. -/
theorem original_primitive_stratum
    (s : Finset κ) (B : κ → ι → ℤ)
    (f : P →ₗ[ℤ] (κ →₀ ℤ)) (basis : Basis ι ℤ P)
    (hf : ∀ i, f (basis i) = column s (fun a => B a i) (fun k => Finsupp.single k 1))
    (hinj : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f))
    (j : τ → κ) (other : τ → OriginalStratum R ι κ) :
    Nonempty ((MvPolynomial (ι ⊕ τ) (OriginalStratum R ι κ) ⧸
      exchangeIdeal (initialCoordinates R ι κ j)
        (Sum.elim (fun i => originalExchange R ι κ s (fun a => B a i)) other)) ≃+*
      MvPolynomial ι (MonoidAlgebra R (Multiplicative ((κ →₀ ℤ) ⧸ LinearMap.range f)))) := by
  let e := originalTorusEquiv R ι κ
  let x := initialCoordinates R ι κ j
  let g := Sum.elim (fun i => originalExchange R ι κ s (fun a => B a i)) other
  have hg : (fun v => e (g v)) = Sum.elim
      (fun i => exchange (R := R) s (fun a => B a i) (fun k => Finsupp.single k 1))
      (fun t => e (other t)) := by
    funext v
    cases v with
    | inl i => exact originalTorusEquiv_exchange R ι κ s (fun a => B a i)
    | inr t => rfl
  have hx0 : ∀ i, e (x (Sum.inl i)) = 0 := by
    intro i
    rw [show x (Sum.inl i) = 0 from initialCoordinates_zero R ι κ j i, map_zero]
  have hxu : ∀ t, e (x (Sum.inr t)) =
      (Units.map e.toMonoidHom (coordinateUnit R ι κ (j t)) : Torus R κ) := by
    intro t
    exact congrArg e (initialCoordinates_unit R ι κ j t)
  obtain ⟨q⟩ := primitive_exchange_stratum (R := R) s B
    (fun k => Finsupp.single k 1) f basis hf hinj hs (fun v => e (x v))
    (fun t => Units.map e.toMonoidHom (coordinateUnit R ι κ (j t))) hx0 hxu
    (fun t => e (other t))
  have q0 := quotientTransport e.toRingEquiv x g
  change (MvPolynomial (ι ⊕ τ) (OriginalStratum R ι κ) ⧸ exchangeIdeal x g) ≃+*
    (MvPolynomial (ι ⊕ τ) (Torus R κ) ⧸ exchangeIdeal (fun v => e (x v))
      (fun v => e (g v))) at q0
  rw [hg] at q0
  exact ⟨q0.trans q⟩

#print axioms map_exchangeIdeal
#print axioms quotientTransport
#print axioms originalExchange
#print axioms originalTorusEquiv_coordinate
#print axioms originalTorusEquiv_exchange
#print axioms initialCoordinates
#print axioms initialCoordinates_zero
#print axioms initialCoordinates_unit
#print axioms original_primitive_stratum
end Verification.CoordinateTransport
