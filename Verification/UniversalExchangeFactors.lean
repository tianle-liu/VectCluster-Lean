/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.UniversalExchangeMaps

/-!
# Universal Exchange Factors

Separation of disjoint sets of xy-1 factors, by explicit inverse maps
of their polynomial localizations.
-/
noncomputable section
namespace Verification.UniversalExchangeFactors
open Verification.UniversalExchangeChart Verification.UniversalExchangeMaps
variable (R ι κ : Type) [CommRing R]
attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev Flat := OpenPolynomial R (ι ⊕ κ)
abbrev Nested := OpenPolynomial (OpenPolynomial R ι) κ

def inner : OpenPolynomial R ι →ₐ[R] Flat R ι κ :=
  lift (Algebra.ofId R (Flat R ι κ))
    (fun i => x R (ι ⊕ κ) (Sum.inl i)) (fun i => y R (ι ⊕ κ) (Sum.inl i))
    (fun i => determinant_unit R (ι ⊕ κ) (Sum.inl i))

def flatten : Nested R ι κ →ₐ[R] Flat R ι κ :=
  lift (inner R ι κ)
    (fun i => x R (ι ⊕ κ) (Sum.inr i)) (fun i => y R (ι ⊕ κ) (Sum.inr i))
    (fun i => determinant_unit R (ι ⊕ κ) (Sum.inr i))

def expand : Flat R ι κ →ₐ[R] Nested R ι κ :=
  lift (Algebra.ofId R (Nested R ι κ))
    (Sum.elim (fun i => algebraMap (OpenPolynomial R ι) (Nested R ι κ) (x R ι i))
      (x (OpenPolynomial R ι) κ))
    (Sum.elim (fun i => algebraMap (OpenPolynomial R ι) (Nested R ι κ) (y R ι i))
      (y (OpenPolynomial R ι) κ)) (by
        intro i
        cases i with
        | inl i =>
            simpa only [map_sub, map_mul, map_one] using
              (determinant_unit R ι i).map (algebraMap (OpenPolynomial R ι) (Nested R ι κ))
        | inr i => exact determinant_unit (OpenPolynomial R ι) κ i)

theorem flatten_expand : (flatten R ι κ).comp (expand R ι κ) = AlgHom.id R _ := by
  apply hom_ext
  · intro r
    simp only [AlgHom.comp_apply, AlgHom.commutes, AlgHom.id_apply]
  · intro i
    cases i <;> simp [flatten, expand, inner]
  · intro i
    cases i <;> simp [flatten, expand, inner]

theorem expand_inner : (expand R ι κ).comp (inner R ι κ) =
    IsScalarTower.toAlgHom R (OpenPolynomial R ι) (Nested R ι κ) := by
  apply hom_ext
  · intro r
    simp only [AlgHom.comp_apply, AlgHom.commutes]
  · intro i
    simp [inner, expand]
  · intro i
    simp [inner, expand]

theorem expand_flatten : (expand R ι κ).comp (flatten R ι κ) = AlgHom.id R _ := by
  apply hom_ext
  · intro c
    change expand R ι κ (flatten R ι κ (algebraMap (OpenPolynomial R ι) (Nested R ι κ) c)) = _
    rw [flatten, lift_coefficient]
    exact AlgHom.congr_fun (expand_inner R ι κ) c
  · intro i
    simp [flatten, expand]
  · intro i
    simp [flatten, expand]

def factorsEquiv : Nested R ι κ ≃ₐ[R] Flat R ι κ :=
  AlgEquiv.ofAlgHom (flatten R ι κ) (expand R ι κ)
    (flatten_expand R ι κ) (expand_flatten R ι κ)

#print axioms Flat
#print axioms Nested
#print axioms inner
#print axioms flatten
#print axioms expand
#print axioms flatten_expand
#print axioms expand_inner
#print axioms expand_flatten
#print axioms factorsEquiv
end Verification.UniversalExchangeFactors
