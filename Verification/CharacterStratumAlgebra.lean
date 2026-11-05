/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CharacterStratum
import Verification.LocallyClosedAlgebra

/-!
# Character Stratum Algebra

The anticlique zero-stratum equation before the AS specialization.
The actual global locally closed ring is a polynomial algebra over the
original finite character-equation quotient. No saturation, rank, or
tameness is required for this identification.
-/
namespace Verification.CharacterStratumAlgebra
open Verification.StratumPresentation Verification.ExchangeCharacters
open Verification.CoordinateTransport Verification.OriginalTorus
open Verification.ActualStratum Verification.LocallyClosedPresentation
open Verification.PrimitiveCharacters
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {R M P α ι κ : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P]

noncomputable def quotientTransport {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (x g : (ι ⊕ κ) → A) :
    (MvPolynomial (ι ⊕ κ) A ⧸ exchangeIdeal x g) ≃ₐ[R]
      (MvPolynomial (ι ⊕ κ) B ⧸ exchangeIdeal (fun v => e (x v)) (fun v => e (g v))) :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.mapAlgEquiv _ e)
    (Verification.CoordinateTransport.map_exchangeIdeal e.toRingEquiv x g).symm

noncomputable def exchangeFiberStratum
    (s : Finset α) (B : α → ι → ℤ) (e : α → M)
    (f : P →ₗ[ℤ] M) (basis : Basis ι ℤ P)
    (hf : ∀ i, f (basis i) = column s (fun a => B a i) e)
    (x : (ι ⊕ κ) → MonoidAlgebra R (Multiplicative M))
    (a : κ → (MonoidAlgebra R (Multiplicative M))ˣ)
    (hx0 : ∀ i, x (Sum.inl i) = 0)
    (hxu : ∀ k, x (Sum.inr k) = (a k : MonoidAlgebra R (Multiplicative M)))
    (other : κ → MonoidAlgebra R (Multiplicative M)) :
    (MvPolynomial (ι ⊕ κ) (MonoidAlgebra R (Multiplicative M)) ⧸
      exchangeIdeal x (Sum.elim (fun i => exchange s (fun a => B a i) e) other)) ≃ₐ[R]
      MvPolynomial ι (MonoidAlgebra R (Multiplicative M) ⧸ prescribedIdeal (R := R) f basis (fun _ => -1)) :=
  (quotientEquiv x (Sum.elim (fun i => exchange s (fun a => B a i) e) other) a hx0 hxu).restrictScalars R |>.trans
    (MvPolynomial.mapAlgEquiv ι (Ideal.quotientEquivAlgOfEq R (exchange_ideal_eq_prescribed s B e f basis hf)))

variable (R ι κ τ : Type*) [CommRing R]

noncomputable def originalFiberStratum
    (s : Finset κ) (B : κ → ι → ℤ)
    (f : P →ₗ[ℤ] (κ →₀ ℤ)) (basis : Basis ι ℤ P)
    (hf : ∀ i, f (basis i) = column s (fun a => B a i) (fun k => Finsupp.single k 1))
    (j : τ → κ) (other : τ → OriginalStratum R ι κ) :
    (MvPolynomial (ι ⊕ τ) (OriginalStratum R ι κ) ⧸
      exchangeIdeal (initialCoordinates R ι κ j)
        (Sum.elim (fun i => originalExchange R ι κ s (fun a => B a i)) other)) ≃ₐ[R]
      MvPolynomial ι (MonoidAlgebra R (Multiplicative (κ →₀ ℤ)) ⧸
        prescribedIdeal (R := R) f basis (fun _ => -1)) := by
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
  let q := exchangeFiberStratum (R := R) s B (fun k => Finsupp.single k 1)
    f basis hf (fun v => e (x v))
    (fun t => Units.map e.toMonoidHom (coordinateUnit R ι κ (j t))) hx0 hxu
    (fun t => e (other t))
  have q0 := quotientTransport e x g
  change (MvPolynomial (ι ⊕ τ) (OriginalStratum R ι κ) ⧸ exchangeIdeal x g) ≃ₐ[R]
    (MvPolynomial (ι ⊕ τ) (Torus R κ) ⧸ exchangeIdeal (fun v => e (x v))
      (fun v => e (g v))) at q0
  rw [hg] at q0
  exact q0.trans q

variable [Fintype ι] [Fintype κ]

noncomputable def globalFiberStratum
    (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0)
    (f : P →ₗ[ℤ] (κ →₀ ℤ)) (basis : Basis ι ℤ P)
    (hf : ∀ i, f (basis i) = column Finset.univ
      (fun a => B (Sum.inr a) (Sum.inl i)) (fun k => Finsupp.single k 1)) :
    GlobalZeroStratum R ι κ τ j B ≃ₐ[R]
      MvPolynomial ι (MonoidAlgebra R (Multiplicative (κ →₀ ℤ)) ⧸
        prescribedIdeal (R := R) f basis (fun _ => -1)) := by
  let other : τ → OriginalStratum R ι κ :=
    fun t => originalBaseMap R ι κ (exchangePolynomial R ι κ τ B (Sum.inr t))
  have hg : (fun v => originalBaseMap R ι κ (exchangePolynomial R ι κ τ B v)) =
      Sum.elim (fun i => originalExchange R ι κ Finset.univ
        (fun a => B (Sum.inr a) (Sum.inl i))) other := by
    funext v
    cases v with
    | inl i => exact exchangePolynomial_map_zero_column R ι κ τ B i (fun a => hB a i)
    | inr t => rfl
  have e := (Verification.LocallyClosedAlgebra.locallyClosedEquivAlg (zeroCoordinateIdeal R ι κ)
    (initialPolynomial R ι κ τ j) (exchangePolynomial R ι κ τ B)
    (fun k : κ => (MvPolynomial.X (Sum.inr k) : OriginalPolynomial R ι κ))).restrictScalars R
  change GlobalZeroStratum R ι κ τ j B ≃ₐ[R]
    (MvPolynomial (ι ⊕ τ) (OriginalStratum R ι κ) ⧸ exchangeIdeal
      (fun v => originalBaseMap R ι κ (initialPolynomial R ι κ τ j v))
      (fun v => originalBaseMap R ι κ (exchangePolynomial R ι κ τ B v))) at e
  rw [initialPolynomial_map, hg] at e
  exact e.trans (originalFiberStratum R ι κ τ Finset.univ
    (fun a i => B (Sum.inr a) (Sum.inl i)) f basis hf j other)

#print axioms quotientTransport
#print axioms exchangeFiberStratum
#print axioms originalFiberStratum
#print axioms globalFiberStratum
end Verification.CharacterStratumAlgebra
