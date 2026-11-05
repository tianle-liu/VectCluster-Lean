/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeLocalCone

/-!
# Prime Canonical Cone

Cardinality transport of the canonical localized pair. This explicit
formula agrees with PrimeLocalCone.layerIso, including its cone map, so
using a fixed chart does not change the global termwise purity choice.
-/
noncomputable section
namespace Verification.PrimeCanonicalCone
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.PrimeCoordinateFiltration Verification.PrimeLayerCover
open Verification.PrimeLocalPair
universe w
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop)
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ) (r : ℕ) (I : Index Allowed r)

def punctureIso :
    (CoordinatePurityInput.puncture (OpenRing A V x I.val) I.val (coordinate A V x I.val)).toScheme ≅
      ((stage x r ⊓ chartOpen A V x I.val) : (Spec (CommRingCat.of A)).Opens).toScheme :=
  PrimeLocalPair.punctureIso A V x I.val ≪≫
    (Spec (CommRingCat.of A)).isoOfEq (by dsimp only [previous]; rw [I.property.1])

omit [HasBinaryBiproducts C] [HasDerivedCategory C] in
theorem pair_square :
    CoordinatePurityInput.pairArrow (OpenRing A V x I.val) I.val (coordinate A V x I.val) G ≫
      G.map (ambientIso A V x I.val).hom =
    G.map (punctureIso A V x Allowed r I).hom ≫
      OpenConeExcision.localArrow (Spec (CommRingCat.of A)) (PrimeLayerExcision.openChains A G)
        (stage x r) (chart x Allowed r) I := by
  rcases I with ⟨I,hc,hI⟩
  subst r
  simpa only [punctureIso,previous,Scheme.isoOfEq_rfl,Iso.trans_refl] using
    PrimeLocalCone.pair_square A V x I G

def relativeIso :
    CoordinatePurityInput.relative (OpenRing A V x I.val) I.val (coordinate A V x I.val) G ≅
      PrimeLayerExcision.localRelative A V x Allowed G r I :=
  ConeDerivedComparison.coneIso _ _ (G.map (punctureIso A V x Allowed r I).hom)
    (G.map (ambientIso A V x I.val).hom) (pair_square A V x Allowed G r I)

theorem relativeIso_eq : relativeIso A V x Allowed G r I = PrimeLocalCone.layerIso A V x G Allowed r I := by
  rcases I with ⟨I,hc,hI⟩
  subst r
  simp only [relativeIso,punctureIso,previous,Scheme.isoOfEq_rfl,Iso.trans_refl]
  rfl

#print axioms punctureIso
#print axioms pair_square
#print axioms relativeIso
#print axioms relativeIso_eq
end Verification.PrimeCanonicalCone
