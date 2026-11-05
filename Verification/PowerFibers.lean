/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Separable
import Mathlib.Dynamics.Newton
import Mathlib.RingTheory.Etale.Field

/-!
# Power Fibers

Power equations in the Smith-coordinate description of character fibers.
The algebra is the actual quotient k[X]/(X^e-b). Formal etaleness is proved
by the square-zero lifting definition, not assumed from separability.
Smith normal form and the geometric comparison to the full stratum are
outside this file.
-/

universe u v

namespace Verification.PowerFibers

open Polynomial

section SeparableQuotients

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

theorem derivative_unit_at_root (p : R[X]) (hp : p.Separable) (x : S)
    (hx : aeval x p = 0) : IsUnit (aeval x p.derivative) := by
  have hc := IsCoprime.map hp (aeval x).toRingHom
  change IsCoprime (aeval x p) (aeval x p.derivative) at hc
  rw [hx] at hc
  exact isCoprime_zero_left.mp hc

theorem separable_roots_rigid (p : R[X]) (hp : p.Separable) (x y : S)
    (hx : aeval x p = 0) (hy : aeval y p = 0) (hxy : IsNilpotent (x - y)) :
    x = y := by
  have hnil : IsNilpotent (aeval x p) := by rw [hx]; exact ⟨1, by simp⟩
  have he := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero hnil
    (derivative_unit_at_root p hp x hx)
  exact he.unique ⟨by simp, hx⟩ ⟨hxy, hy⟩

theorem nilpotent_of_mem_square_zero (J : Ideal S) (hJ : J ^ 2 = ⊥)
    (x : S) (hx : x ∈ J) : IsNilpotent x := by
  refine ⟨2, ?_⟩
  rw [← Ideal.mem_bot, ← hJ]
  exact Ideal.pow_mem_pow hx 2

/-- A separable polynomial quotient satisfies the actual unique-lifting
definition of formal etaleness. This holds over any commutative base ring. -/
theorem separable_adjoinRoot_formallyEtale (p : R[X]) (hp : p.Separable) :
    Algebra.FormallyEtale R (AdjoinRoot p) := by
  constructor
  intro B _ _ J hJ
  constructor
  · intro g h hgh
    apply AdjoinRoot.algHom_ext
    apply separable_roots_rigid p hp
    · exact AdjoinRoot.aeval_algHom_eq_zero p g
    · exact AdjoinRoot.aeval_algHom_eq_zero p h
    · apply nilpotent_of_mem_square_zero J hJ
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have he := congrArg (fun f : AdjoinRoot p →ₐ[R] B ⧸ J => f (AdjoinRoot.root p)) hgh
      change Ideal.Quotient.mk J (g (AdjoinRoot.root p)) =
        Ideal.Quotient.mk J (h (AdjoinRoot.root p)) at he
      rw [map_sub, he, sub_self]
  · intro f
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (f (AdjoinRoot.root p))
    have hpq : Ideal.Quotient.mk J (aeval x p) = 0 := by
      change (Ideal.Quotient.mkₐ R J) (aeval x p) = 0
      rw [← Polynomial.aeval_algHom_apply]
      change aeval (Ideal.Quotient.mk J x) p = 0
      rw [hx]
      exact AdjoinRoot.aeval_algHom_eq_zero p f
    have hpnil : IsNilpotent (aeval x p) :=
      nilpotent_of_mem_square_zero J hJ _ (Ideal.Quotient.eq_zero_iff_mem.mp hpq)
    have hduq : IsUnit (Ideal.Quotient.mk J (aeval x p.derivative)) := by
      change IsUnit ((Ideal.Quotient.mkₐ R J) (aeval x p.derivative))
      rw [← Polynomial.aeval_algHom_apply]
      change IsUnit (aeval (Ideal.Quotient.mk J x) p.derivative)
      rw [hx]
      exact derivative_unit_at_root p hp _ (AdjoinRoot.aeval_algHom_eq_zero p f)
    have hJnil : IsNilpotent J := ⟨2, hJ⟩
    have hdu : IsUnit (aeval x p.derivative) := hJnil.isUnit_quotient_mk_iff.mp hduq
    obtain ⟨r, ⟨hnil, hr⟩, _⟩ :=
      Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero hpnil hdu
    refine ⟨AdjoinRoot.liftHom p r hr, ?_⟩
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, AdjoinRoot.liftHom_root]
    change Ideal.Quotient.mk J r = f (AdjoinRoot.root p)
    apply Eq.symm
    apply separable_roots_rigid p hp
    · exact AdjoinRoot.aeval_algHom_eq_zero p f
    · change aeval ((Ideal.Quotient.mkₐ R J) r) p = 0
      rw [Polynomial.aeval_algHom_apply, hr, map_zero]
    · have h := hnil.map (Ideal.Quotient.mk J)
      simpa only [map_sub, hx] using h

theorem separable_adjoinRoot_etale (p : R[X]) (hp : p.Separable) :
    Algebra.Etale R (AdjoinRoot p) where
  formallyEtale := separable_adjoinRoot_formallyEtale p hp
  finitePresentation := AdjoinRoot.finitePresentation p

end SeparableQuotients

section PowerEquation

variable (k : Type u) [Field k]

noncomputable def powerPolynomial (e : ℕ) (b : kˣ) : k[X] := X ^ e - C (b : k)

/-- Definitionally the quotient by the principal ideal (X^e-b). -/
abbrev Fiber (e : ℕ) (b : kˣ) := AdjoinRoot (powerPolynomial k e b)

theorem power_polynomial_monic (e : ℕ) (he : 0 < e) (b : kˣ) :
    (powerPolynomial k e b).Monic := monic_X_pow_sub_C (b : k) (Nat.ne_of_gt he)

theorem power_polynomial_separable (e : ℕ) (he : (e : k) ≠ 0) (b : kˣ) :
    (powerPolynomial k e b).Separable :=
  Polynomial.separable_X_pow_sub_C (b : k) he b.ne_zero

theorem power_polynomial_separable_char (p e : ℕ) [CharP k p]
    (he : ¬p ∣ e) (b : kˣ) : (powerPolynomial k e b).Separable :=
  Polynomial.separable_X_pow_sub_C' p e (b : k) he b.ne_zero

theorem fiber_formallyEtale (e : ℕ) (he : (e : k) ≠ 0) (b : kˣ) :
    Algebra.FormallyEtale k (Fiber k e b) :=
  separable_adjoinRoot_formallyEtale _ (power_polynomial_separable k e he b)

theorem fiber_etale (e : ℕ) (he : (e : k) ≠ 0) (b : kˣ) :
    Algebra.Etale k (Fiber k e b) :=
  separable_adjoinRoot_etale _ (power_polynomial_separable k e he b)

theorem fiber_finite (e : ℕ) (he : 0 < e) (b : kˣ) :
    Module.Finite k (Fiber k e b) := (power_polynomial_monic k e he b).finite_adjoinRoot

theorem fiber_free (e : ℕ) (he : 0 < e) (b : kˣ) :
    Module.Free k (Fiber k e b) := (power_polynomial_monic k e he b).free_adjoinRoot

/-- The exact tame-exponent hypothesis needed in the Smith-coordinate step. -/
theorem fiber_finite_etale_of_char (p e : ℕ) [CharP k p]
    (he : ¬p ∣ e) (b : kˣ) :
    Module.Finite k (Fiber k e b) ∧ Algebra.Etale k (Fiber k e b) := by
  have hpos : 0 < e := Nat.pos_of_ne_zero (fun h => he (h ▸ dvd_zero p))
  exact ⟨fiber_finite k e hpos b,
    separable_adjoinRoot_etale _ (power_polynomial_separable_char k p e he b)⟩

theorem fiber_finrank (e : ℕ) (he : 0 < e) (b : kˣ) :
    Module.finrank k (Fiber k e b) = e := by
  have h := (AdjoinRoot.powerBasis' (power_polynomial_monic k e he b)).finrank
  simpa [AdjoinRoot.powerBasis', powerPolynomial, Polynomial.natDegree_X_pow_sub_C] using h

theorem root_power (e : ℕ) (b : kˣ) :
    AdjoinRoot.root (powerPolynomial k e b) ^ e = algebraMap k (Fiber k e b) (b : k) := by
  have h := AdjoinRoot.eval₂_root (powerPolynomial k e b)
  simpa [powerPolynomial, sub_eq_zero] using h

theorem root_isUnit (e : ℕ) (he : 0 < e) (b : kˣ) :
    IsUnit (AdjoinRoot.root (powerPolynomial k e b)) := by
  apply (isUnit_pow_iff (Nat.ne_of_gt he)).mp
  rw [root_power]
  exact b.isUnit.map (algebraMap k (Fiber k e b))

/-- Inverting the coordinate X after imposing X^e=b changes no algebra. -/
noncomputable def invertRootEquiv (e : ℕ) (he : 0 < e) (b : kˣ) :
    Fiber k e b ≃ₐ[Fiber k e b]
      Localization.Away (AdjoinRoot.root (powerPolynomial k e b)) :=
  IsLocalization.atUnit (Fiber k e b)
    (Localization.Away (AdjoinRoot.root (powerPolynomial k e b)))
    (AdjoinRoot.root (powerPolynomial k e b)) (root_isUnit k e he b)

theorem root_derivative_isUnit (e : ℕ) (he : (e : k) ≠ 0) (b : kˣ) :
    IsUnit (aeval (AdjoinRoot.root (powerPolynomial k e b))
      (powerPolynomial k e b).derivative) := by
  apply derivative_unit_at_root _ (power_polynomial_separable k e he b)
  simp

/-- The finite etale factor in a Smith stratum splits as a finite product
of finite separable field extensions; no algebraic-closure assumption. -/
theorem fiber_finite_separable_product (e : ℕ) (he : (e : k) ≠ 0) (b : kˣ) :
    ∃ (ι : Type u) (_ : Finite ι) (L : ι → Type u) (_ : ∀ i, Field (L i))
      (_ : ∀ i, Algebra k (L i)) (_ : Fiber k e b ≃ₐ[k] ∀ i, L i),
      ∀ i, Module.Finite k (L i) ∧ Algebra.IsSeparable k (L i) :=
  (Algebra.Etale.iff_exists_algEquiv_prod k (Fiber k e b)).mp (fiber_etale k e he b)

end PowerEquation

end Verification.PowerFibers

-- Audit every theorem and definition, including the actual quotient algebra.
#print axioms Verification.PowerFibers.derivative_unit_at_root
#print axioms Verification.PowerFibers.separable_roots_rigid
#print axioms Verification.PowerFibers.nilpotent_of_mem_square_zero
#print axioms Verification.PowerFibers.separable_adjoinRoot_formallyEtale
#print axioms Verification.PowerFibers.separable_adjoinRoot_etale
#print axioms Verification.PowerFibers.powerPolynomial
#print axioms Verification.PowerFibers.Fiber
#print axioms Verification.PowerFibers.power_polynomial_monic
#print axioms Verification.PowerFibers.power_polynomial_separable
#print axioms Verification.PowerFibers.power_polynomial_separable_char
#print axioms Verification.PowerFibers.fiber_formallyEtale
#print axioms Verification.PowerFibers.fiber_etale
#print axioms Verification.PowerFibers.fiber_finite
#print axioms Verification.PowerFibers.fiber_free
#print axioms Verification.PowerFibers.fiber_finite_etale_of_char
#print axioms Verification.PowerFibers.fiber_finrank
#print axioms Verification.PowerFibers.root_power
#print axioms Verification.PowerFibers.root_isUnit
#print axioms Verification.PowerFibers.invertRootEquiv
#print axioms Verification.PowerFibers.root_derivative_isUnit
#print axioms Verification.PowerFibers.fiber_finite_separable_product
