/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePurityInput
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Torus Thom Input

The cited standard torus--Thom computation, stated uniformly for literal
split torus and affine coordinate rings. The objects here are genuine
scheme-pair cones. Neither an exchange cellular decomposition nor its
boundary formula is an input. K is the independently supplied family of
positive-degree coefficient objects (Milnor--Witt objects in that application).
The zero-weight object Z is separate: it is the integer sheaf, not KMW_0.
-/
noncomputable section
namespace Verification.TorusThomInput
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
universe w
variable (R : Type) [CommRing R]
variable (ι τ κ : Type) [Fintype ι] [Fintype τ] [Fintype κ]

abbrev BaseRing := MvPolynomial τ (MonoidAlgebra R (Multiplicative (κ →₀ ℤ)))
abbrev NormalRing := MvPolynomial ι (BaseRing R τ κ)

variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def thom : DerivedCategory C := CoordinatePurityInput.relative (NormalRing R ι τ κ) ι MvPolynomial.X G

variable (Z : C) (K : ℕ → C)

def symbolTerms : C := ⨁ fun A : Finset κ => if Fintype.card ι + A.card = 0 then Z else K (Fintype.card ι + A.card)

/-- Uniform standard calculation, including affine homotopy invariance.
The required hypotheses on the base and on G belong to the theorem that
supplies this structure, and are not silently inferred from commutativity. -/
structure StandardTorusThom where
  homologyIso : ∀ (ι τ κ : Type) [Fintype ι] [Fintype τ] [Fintype κ],
    (DerivedCategory.homologyFunctor C (-(Fintype.card ι : ℤ))).obj (thom R ι τ κ G) ≅
      symbolTerms ι κ Z K
  concentrated : ∀ (ι τ κ : Type) [Fintype ι] [Fintype τ] [Fintype κ] (q : ℤ),
    q ≠ -(Fintype.card ι : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor C q).obj (thom R ι τ κ G))

#print axioms BaseRing
#print axioms NormalRing
#print axioms thom
#print axioms symbolTerms
#print axioms StandardTorusThom
end Verification.TorusThomInput
