/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePairReindex

/-!
# Coordinate Pair Transport

Functorial coordinate transport with both an index equivalence and
an actual ring equivalence. All cone maps are determined by the genuine
scheme and punctured-scheme maps.
-/
noncomputable section
namespace Verification.CoordinatePairTransport
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinatePurityInput
variable {A B E ι κ τ : Type} [CommRing A] [CommRing B] [CommRing E]
variable (x : ι → A) (y : κ → B) (z : τ → E)
variable (u : κ ≃ ι) (v : τ ≃ κ) (e : A ≃+* B) (f : B ≃+* E)
variable (he : ∀ i, e (x (u i)) = y i) (hf : ∀ i, f (y (v i)) = z i)

def openIso : (puncture A ι x).toScheme ≅ (puncture B κ y).toScheme :=
  CoordinatePairReindex.openIso A ι κ x u ≪≫ CoordinatePairEquiv.punctureIso (x ∘ u) y e he

theorem open_square : (openIso x y u e he).hom ≫ (puncture B κ y).ι =
    (puncture A ι x).ι ≫ (CoordinatePairEquiv.schemeIso e).hom := by
  rw [openIso,Iso.trans_hom,Category.assoc,← CoordinatePairEquiv.puncture_square,
    ← Category.assoc,CoordinatePairReindex.open_square]

theorem scheme_comp : (CoordinatePairEquiv.schemeIso e).hom ≫ (CoordinatePairEquiv.schemeIso f).hom =
    (CoordinatePairEquiv.schemeIso (e.trans f)).hom := by
  simp only [CoordinatePairEquiv.schemeIso,Functor.mapIso_hom,← Functor.map_comp]
  rfl

theorem open_comp : (openIso x y u e he).hom ≫ (openIso y z v f hf).hom =
    (openIso x z (v.trans u) (e.trans f) (fun i => by
      change f (e (x (u (v i)))) = z i
      rw [he,hf])).hom := by
  apply (cancel_mono (puncture E τ z).ι).1
  simp only [Category.assoc,open_square]
  rw [← Category.assoc,open_square,Category.assoc,scheme_comp]

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def relativeIso : relative A ι x G ≅ relative B κ y G :=
  CoordinatePairReindex.relativeIso A ι κ x u G ≪≫ CoordinatePairEquiv.relativeIso (x ∘ u) y e he G

theorem relativeIso_hom : (relativeIso x y u e he G).hom =
    TransverseDerivedBoundary.coneMap (pairArrow A ι x G) (pairArrow B κ y G)
      (G.map (openIso x y u e he).hom) (G.map (CoordinatePairEquiv.schemeIso e).hom)
      (by simpa only [pairArrow,← Functor.map_comp] using congrArg G.map (open_square x y u e he).symm) := by
  simp only [relativeIso,Iso.trans_hom,CoordinatePairReindex.relativeIso,CoordinatePairEquiv.relativeIso,
    ConeDerivedComparison.coneIso,asIso_hom,TransverseDerivedBoundary.coneMap,TransverseConeBoundary.coneMap,
    ← Functor.map_comp,← mappingCone.map_comp,Category.id_comp,openIso,Iso.trans_hom]

theorem relative_comp : (relativeIso x y u e he G).hom ≫ (relativeIso y z v f hf G).hom =
    (relativeIso x z (v.trans u) (e.trans f) (fun i => by
      change f (e (x (u (v i)))) = z i
      rw [he,hf]) G).hom := by
  simp only [relativeIso_hom,TransverseDerivedBoundary.coneMap,TransverseConeBoundary.coneMap,
    ← Functor.map_comp,← mappingCone.map_comp,open_comp,scheme_comp]

#print axioms openIso
#print axioms open_square
#print axioms scheme_comp
#print axioms open_comp
#print axioms relativeIso
#print axioms relativeIso_hom
#print axioms relative_comp
end Verification.CoordinatePairTransport
