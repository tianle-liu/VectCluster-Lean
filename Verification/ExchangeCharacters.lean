/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimitiveCharacters
import Verification.TranslatedStratum
import Mathlib.Algebra.Group.Units.Hom
import Lean.Elab.Tactic.Omega

/-!
# Exchange Characters

The actual positive/negative exchange monomials give the character
equation chi = -1. The unit factor is constructed from the negative
exponent vector. This is the algebraic step at manuscript.tex:375--377,
and connects the primitive-fiber theorem to literal exchange polynomials.
-/
namespace Verification.ExchangeCharacters
open scoped BigOperators
open MonoidAlgebra
variable {R M α ι κ : Type*} [CommRing R] [AddCommGroup M]

def column (s : Finset α) (b : α → ℤ) (e : α → M) : M :=
  ∑ a ∈ s, b a • e a

def positive (s : Finset α) (b : α → ℤ) (e : α → M) : M :=
  ∑ a ∈ s, ((b a).toNat : ℤ) • e a

def negative (s : Finset α) (b : α → ℤ) (e : α → M) : M :=
  ∑ a ∈ s, ((-b a).toNat : ℤ) • e a

theorem positive_eq_negative_add_column (s : Finset α) (b : α → ℤ) (e : α → M) :
    positive s b e = negative s b e + column s b e := by
  unfold positive negative column
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have h : ((b a).toNat : ℤ) = ((-b a).toNat : ℤ) + b a := by omega
  rw [h, add_smul]

noncomputable def monomial (m : M) : MonoidAlgebra R (Multiplicative M) :=
  of R (Multiplicative M) (Multiplicative.ofAdd m)

@[simp] theorem monomial_zero : monomial (R := R) (0 : M) = 1 :=
  (of R (Multiplicative M)).map_one

theorem monomial_add (m n : M) :
    monomial (R := R) (m + n) = monomial m * monomial n :=
  (of R (Multiplicative M)).map_mul _ _

theorem monomial_nsmul (n : ℕ) (m : M) :
    monomial (R := R) (n • m) = monomial m ^ n :=
  (of R (Multiplicative M)).map_pow _ _

theorem monomial_sum (s : Finset α) (v : α → M) :
    monomial (R := R) (∑ a ∈ s, v a) = ∏ a ∈ s, monomial (v a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, monomial_add, ih]

theorem positive_monomial (s : Finset α) (b : α → ℤ) (e : α → M) :
    monomial (R := R) (positive s b e) = ∏ a ∈ s, monomial (e a) ^ (b a).toNat := by
  rw [positive, monomial_sum]
  apply Finset.prod_congr rfl
  intro a ha
  simpa only [natCast_zsmul] using monomial_nsmul (R := R) (b a).toNat (e a)

theorem negative_monomial (s : Finset α) (b : α → ℤ) (e : α → M) :
    monomial (R := R) (negative s b e) = ∏ a ∈ s, monomial (e a) ^ (-b a).toNat := by
  exact positive_monomial s (fun a => -b a) e

noncomputable def negativeUnit (s : Finset α) (b : α → ℤ) (e : α → M) :
    (MonoidAlgebra R (Multiplicative M))ˣ :=
  (of R (Multiplicative M)).toHomUnits (Multiplicative.ofAdd (negative s b e))

noncomputable def exchange (s : Finset α) (b : α → ℤ) (e : α → M) :
    MonoidAlgebra R (Multiplicative M) :=
  (∏ a ∈ s, monomial (e a) ^ (b a).toNat) +
    ∏ a ∈ s, monomial (e a) ^ (-b a).toNat

/-- Literal exchange monomials, including both positive and negative parts. -/
theorem exchange_factor (s : Finset α) (b : α → ℤ) (e : α → M) :
    exchange (R := R) s b e =
      (negativeUnit (R := R) s b e : MonoidAlgebra R (Multiplicative M)) *
        (monomial (column s b e) - algebraMap R _ (-1)) := by
  change exchange s b e = monomial (negative s b e) *
    (monomial (column s b e) - algebraMap R _ (-1))
  rw [exchange, ← positive_monomial, ← negative_monomial,
    positive_eq_negative_add_column, monomial_add]
  simp only [map_neg, map_one, sub_neg_eq_add, mul_add, mul_one]

variable {P : Type*} [AddCommGroup P]

theorem exchange_ideal_eq_prescribed (s : Finset α) (B : α → ι → ℤ) (e : α → M)
    (f : P →ₗ[ℤ] M) (basis : Basis ι ℤ P)
    (hf : ∀ i, f (basis i) = column s (fun a => B a i) e) :
    Ideal.span (Set.range (fun i => exchange (R := R) s (fun a => B a i) e)) =
      Verification.PrimitiveCharacters.prescribedIdeal f basis (fun _ => -1) := by
  unfold Verification.PrimitiveCharacters.prescribedIdeal
  have he : (fun i => exchange (R := R) s (fun a => B a i) e) =
      fun i => (negativeUnit (R := R) s (fun a => B a i) e : MonoidAlgebra R (Multiplicative M)) *
        (monomial (f (basis i)) - algebraMap R _ (-1)) := by
    funext i
    rw [hf, exchange_factor]
  rw [he, Verification.TranslatedStratum.unit_scaled_span]
  rfl

/-- Primitive columns give the split torus directly from exchange equations. -/
theorem primitive_exchange_fiber [Module.Finite ℤ M]
    (s : Finset α) (B : α → ι → ℤ) (e : α → M)
    (f : P →ₗ[ℤ] M) (basis : Basis ι ℤ P)
    (hf : ∀ i, f (basis i) = column s (fun a => B a i) e)
    (hinj : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    Nonempty ((MonoidAlgebra R (Multiplicative M) ⧸
      Ideal.span (Set.range (fun i => exchange (R := R) s (fun a => B a i) e))) ≃ₐ[R]
      MonoidAlgebra R (Multiplicative (M ⧸ LinearMap.range f))) := by
  rw [exchange_ideal_eq_prescribed s B e f basis hf]
  exact Verification.PrimitiveCharacters.primitive_prescribed_fiber f hinj hs basis (fun _ => -1)

/-- After the prescribed original coordinates vanish, the literal exchange
relations have a polynomial algebra of free partners over the split torus.
Only injectivity and saturation of the original column map are inputs. -/
theorem primitive_exchange_stratum [Module.Finite ℤ M]
    (s : Finset α) (B : α → ι → ℤ) (e : α → M)
    (f : P →ₗ[ℤ] M) (basis : Basis ι ℤ P)
    (hf : ∀ i, f (basis i) = column s (fun a => B a i) e)
    (hinj : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f))
    (x : (ι ⊕ κ) → MonoidAlgebra R (Multiplicative M))
    (a : κ → (MonoidAlgebra R (Multiplicative M))ˣ)
    (hx0 : ∀ i, x (Sum.inl i) = 0)
    (hxu : ∀ k, x (Sum.inr k) = (a k : MonoidAlgebra R (Multiplicative M)))
    (other : κ → MonoidAlgebra R (Multiplicative M)) :
    Nonempty ((MvPolynomial (ι ⊕ κ) (MonoidAlgebra R (Multiplicative M)) ⧸
      Verification.StratumPresentation.exchangeIdeal x
        (Sum.elim (fun i => exchange s (fun a => B a i) e) other)) ≃+*
      MvPolynomial ι (MonoidAlgebra R (Multiplicative (M ⧸ LinearMap.range f)))) := by
  obtain ⟨q⟩ := primitive_exchange_fiber (R := R) s B e f basis hf hinj hs
  refine ⟨(Verification.StratumPresentation.quotientEquiv x
    (Sum.elim (fun i => exchange s (fun a => B a i) e) other) a hx0 hxu).toRingEquiv.trans ?_⟩
  exact MvPolynomial.mapEquiv ι q.toRingEquiv

#print axioms column
#print axioms positive
#print axioms negative
#print axioms positive_eq_negative_add_column
#print axioms monomial
#print axioms monomial_zero
#print axioms monomial_add
#print axioms monomial_nsmul
#print axioms monomial_sum
#print axioms positive_monomial
#print axioms negative_monomial
#print axioms negativeUnit
#print axioms exchange
#print axioms exchange_factor
#print axioms exchange_ideal_eq_prescribed
#print axioms primitive_exchange_fiber
#print axioms primitive_exchange_stratum
end Verification.ExchangeCharacters
