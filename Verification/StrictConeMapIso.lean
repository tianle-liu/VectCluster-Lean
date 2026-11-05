/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ConeDerivedComparison
import Verification.RelativeProductFunctor

/-!
# Strict Cone Map Iso

A cone comparison induced by two strict chain isomorphisms has the
literal inverse induced by their inverse chain maps. This identifies the
canonical raw cone maps used in chart and index changes.
-/
noncomputable section
namespace Verification.StrictConeMapIso
open CategoryTheory CategoryTheory.Limits CochainComplex
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {U₁ W₁ U₂ W₂ : CochainComplex C ℤ}
variable (f : U₁ ⟶ W₁) (g : U₂ ⟶ W₂)
variable (u : U₁ ⟶ U₂) (v : W₁ ⟶ W₂) (h : f ≫ v = u ≫ g)
variable [IsIso u] [IsIso v]

def arrowIso : Arrow.mk f ≅ Arrow.mk g := Arrow.isoMk (asIso u) (asIso v) h.symm

def complexIso : mappingCone f ≅ mappingCone g :=
  RelativeProductFunctor.coneFunctor.mapIso (arrowIso f g u v h)

theorem derived_eq : ConeDerivedComparison.coneIso f g u v h =
    DerivedCategory.Q.mapIso (complexIso f g u v h) := by
  apply Iso.ext
  rfl

include h in
omit [HasBinaryBiproducts C] [HasDerivedCategory C] in
theorem inverse_square : g ≫ inv v = inv u ≫ f := by
  rw [← cancel_epi u, ← Category.assoc, ← h]
  simp only [Category.assoc,IsIso.hom_inv_id,Category.comp_id,IsIso.hom_inv_id_assoc]

theorem inverse_eq : (ConeDerivedComparison.coneIso f g u v h).inv =
    TransverseDerivedBoundary.coneMap g f (inv u) (inv v) (inverse_square f g u v h) := by
  rw [derived_eq]
  rfl

#print axioms arrowIso
#print axioms complexIso
#print axioms derived_eq
#print axioms inverse_square
#print axioms inverse_eq
end Verification.StrictConeMapIso
