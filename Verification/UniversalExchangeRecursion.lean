/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.UniversalExchangeFactors
import Verification.UniversalExchangeTransport
import Verification.HyperbolaGeometry

/-!
# Universal Exchange Recursion

The actual zero-factor model is the coefficient ring, the one-factor
model is D(xy-1), and adding one factor is the corresponding two-variable
principal open over the preceding model.
-/
noncomputable section
namespace Verification.UniversalExchangeRecursion
open Verification.UniversalExchangeChart Verification.UniversalExchangeMaps
variable (R : Type) [CommRing R]
attribute [local instance] MvPolynomial.algebraMvPolynomial

def emptyMap : OpenPolynomial R (Fin 0) →ₐ[R] R :=
  lift (AlgHom.id R R) Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i)

def emptyEquiv : OpenPolynomial R (Fin 0) ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom (emptyMap R) (Algebra.ofId R _) (Subsingleton.elim _ _) (by
    apply hom_ext
    · intro r
      simp only [AlgHom.comp_apply, AlgHom.commutes, AlgHom.id_apply]
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i)

theorem one_product : (∏ i : Fin 1, value R (Fin 1) i) = HyperbolaGeometry.equation R := by
  simp only [Fin.prod_univ_one]
  rfl

def oneEquiv : OpenPolynomial R (Fin 1) ≃ₐ[R]
    Localization.Away (HyperbolaGeometry.equation R) := by
  have e := (SplitExchangeChart.localizationProductEquiv (value R (Fin 1))).restrictScalars R
  rw [one_product R] at e
  exact e

def successorEquiv (n : ℕ) : OpenPolynomial (OpenPolynomial R (Fin n)) (Fin 1) ≃ₐ[R]
    OpenPolynomial R (Fin (n+1)) :=
  (UniversalExchangeFactors.factorsEquiv R (Fin n) (Fin 1)).trans
    (UniversalExchangeTransport.openEquiv (AlgEquiv.refl : R ≃ₐ[R] R) finSumFinEquiv)

#print axioms emptyMap
#print axioms emptyEquiv
#print axioms one_product
#print axioms oneEquiv
#print axioms successorEquiv
end Verification.UniversalExchangeRecursion
