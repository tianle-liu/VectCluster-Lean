/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.UniversalExchangeChart
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Universal Exchange Transport

Changing the coefficient torus and relabeling the factors of the actual
open polynomial model transports its defining equations exactly.
-/
noncomputable section
namespace Verification.UniversalExchangeTransport
open Verification.UniversalExchangeChart
variable {R S T ι κ : Type} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable (e : S ≃ₐ[R] T) (q : ι ≃ κ)

def polynomialEquiv : Polynomial S ι ≃ₐ[R] Polynomial T κ :=
  (MvPolynomial.mapAlgEquiv (σ := ι ⊕ ι) e).trans
    ((MvPolynomial.renameEquiv T (Equiv.sumCongr q q)).restrictScalars R)

theorem polynomialEquiv_X (i : ι ⊕ ι) :
    polynomialEquiv e q (MvPolynomial.X i) = MvPolynomial.X (Equiv.sumCongr q q i) := by
  simp [polynomialEquiv, MvPolynomial.mapAlgEquiv]

theorem polynomialEquiv_value (i : ι) :
    polynomialEquiv e q (value S ι i) = value T κ (q i) := by
  simp only [value, map_sub, map_mul, map_one, polynomialEquiv_X,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]

theorem map_valueMonoid :
    (SplitExchangeChart.valueMonoid (value S ι)).map (polynomialEquiv e q).toMonoidHom =
      SplitExchangeChart.valueMonoid (value T κ) := by
  rw [SplitExchangeChart.valueMonoid, MonoidHom.map_mclosure, ← Set.range_comp]
  congr 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨q i, (polynomialEquiv_value e q i).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨q.symm k, by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      polynomialEquiv_value e q (q.symm k)⟩

def openEquiv : OpenPolynomial S ι ≃ₐ[R] OpenPolynomial T κ :=
  IsLocalization.algEquivOfAlgEquiv _ _ (polynomialEquiv e q) (map_valueMonoid e q)

theorem openEquiv_generator (p : Polynomial S ι) :
    openEquiv e q (algebraMap (Polynomial S ι) (OpenPolynomial S ι) p) =
      algebraMap (Polynomial T κ) (OpenPolynomial T κ) (polynomialEquiv e q p) := by
  change IsLocalization.map
    (M := SplitExchangeChart.valueMonoid (value S ι))
    (T := SplitExchangeChart.valueMonoid (value T κ))
    (OpenPolynomial T κ) (polynomialEquiv e q).toRingHom (by
      intro p hp
      change polynomialEquiv e q p ∈ SplitExchangeChart.valueMonoid (value T κ)
      rw [← map_valueMonoid e q]
      exact ⟨p, hp, rfl⟩)
    (algebraMap (Polynomial S ι) (OpenPolynomial S ι) p) = _
  rw [IsLocalization.map_eq]
  rfl

theorem openEquiv_x (i : ι) :
    openEquiv e q (algebraMap (Polynomial S ι) (OpenPolynomial S ι)
      (MvPolynomial.X (Sum.inl i))) =
      algebraMap (Polynomial T κ) (OpenPolynomial T κ) (MvPolynomial.X (Sum.inl (q i))) := by
  rw [openEquiv_generator, polynomialEquiv_X]
  rfl

#print axioms polynomialEquiv
#print axioms polynomialEquiv_X
#print axioms polynomialEquiv_value
#print axioms map_valueMonoid
#print axioms openEquiv
#print axioms openEquiv_generator
#print axioms openEquiv_x
end Verification.UniversalExchangeTransport
