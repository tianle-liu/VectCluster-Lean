/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostPrincipalResidueInput

/-!
# Rost Unit Transport

Canonical units, inverse cycle comparisons and transported principal
boundaries. These consequences use only ordinary ring-isomorphism/product
naturality, and prescribe no coordinate or component boundary.
-/
noncomputable section
namespace Verification.RostUnitTransport
open CategoryTheory AlgebraicGeometry
open Verification.RostCanonicalCoefficients
variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (U : OriginalRostUnitTerms.UnitsConvention T) (N : UnitsNaturality T F U)
include N

variable (k A B : Type) [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra.Smooth k A] [Algebra.Smooth k B]

theorem iso_inverse (e : A ≃+* B) (u : Additive Aˣ) :
    transport T e 1 ((U.units k A).inv u) =
      (U.units k B).inv
        (Additive.ofMul (Units.map e.toMonoidHom (Additive.toMul u))) := by
  apply (U.units k B).addCommGroupIsoToAddEquiv.injective
  change (U.units k B).hom (transport T e 1 ((U.units k A).inv u)) =
    (U.units k B).hom ((U.units k B).inv _)
  rw [N.iso k A B e, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  rfl

omit [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra.Smooth k A] [Algebra.Smooth k B] in
theorem product_inverse {J : Type} [Fintype J] (R : J → Type)
    [∀ j,CommRing (R j)] [∀ j,Algebra k (R j)] [∀ j,Algebra.Smooth k (R j)]
    [Algebra.Smooth k (∀ j,R j)] (u : Additive (∀ j,R j)ˣ) (j : J) :
    F.product J R 1 0 ((U.units k (∀ j,R j)).inv u) j =
      (U.units k (R j)).inv
        (Additive.ofMul (Units.map (Pi.evalRingHom R j).toMonoidHom (Additive.toMul u))) := by
  apply (U.units k (R j)).addCommGroupIsoToAddEquiv.injective
  change (U.units k (R j)).hom _ = (U.units k (R j)).hom ((U.units k (R j)).inv _)
  have h := N.product k J R ((U.units k (∀ j,R j)).inv u) j
  simp only [Iso.inv_hom_id_apply] at h ⊢
  exact congrArg Additive.ofMul h.symm

variable (P : RostPrincipalLocalizationInput.Theory T)
variable (t : B) (ht : IsRegular t) [Algebra.Smooth k (RostPrincipalLocalizationInput.OpenRing B t)]

/-- Transporting a cycle into the principal open and taking its boundary
is the same as applying the boundary to its actual transported unit. -/
theorem boundary_transport (e : A ≃+* RostPrincipalLocalizationInput.OpenRing B t)
    (a : Sections T A 1) :
    P.boundary k B t ht 1 (transport T e 1 a) =
      RostPrincipalResidueInput.unitBoundary T P U k B t ht
        (Additive.ofMul (Units.map e.toMonoidHom
          (Additive.toMul ((U.units k A).hom a)))) := by
  have h := iso_inverse T F U N k A (RostPrincipalLocalizationInput.OpenRing B t)
    e ((U.units k A).hom a)
  rw [Iso.hom_inv_id_apply] at h
  change P.boundary k B t ht 1 (transport T e 1 a) =
    P.boundary k B t ht 1 ((U.units k (RostPrincipalLocalizationInput.OpenRing B t)).inv _)
  rw [h]
  rfl

#print axioms iso_inverse
#print axioms product_inverse
#print axioms boundary_transport
end Verification.RostUnitTransport
