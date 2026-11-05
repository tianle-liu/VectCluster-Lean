/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeLocalPair
import Verification.ConeDerivedComparison
import Verification.PrimeLayerExcision

/-!
# Prime Local Cone

The punctured original coordinate pair and the actual local cone of the
Zariski filtration are compared by isomorphisms of the underlying schemes.
The comparison is the canonical mapping-cone map and retains its boundary.
-/
noncomputable section
namespace Verification.PrimeLocalCone
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.PrimeLocalPair
universe w
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (I : Finset V)
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def localArrow : G.obj (previous A V x I ⊓ chartOpen A V x I).toScheme ⟶
    G.obj (chartOpen A V x I).toScheme :=
  G.map ((Spec (CommRingCat.of A)).homOfLE inf_le_right)

omit [HasBinaryBiproducts C] [HasDerivedCategory C] in
theorem pair_square :
    CoordinatePurityInput.pairArrow (OpenRing A V x I) I (coordinate A V x I) G ≫
        G.map (ambientIso A V x I).hom =
      G.map (punctureIso A V x I).hom ≫ localArrow A V x I G := by
  simp only [CoordinatePurityInput.pairArrow,localArrow,← CategoryTheory.Functor.map_comp,
    punctureIso_square]

def relativeIso : CoordinatePurityInput.relative (OpenRing A V x I) I (coordinate A V x I) G ≅
    DerivedCategory.Q.obj (mappingCone (localArrow A V x I G)) :=
  ConeDerivedComparison.coneIso _ _ (G.map (punctureIso A V x I).hom)
    (G.map (ambientIso A V x I).hom) (pair_square A V x I G)

theorem relativeIso_boundary : (relativeIso A V x I G).hom ≫
    TransverseDerivedBoundary.boundary (localArrow A V x I G) =
      TransverseDerivedBoundary.boundary
        (CoordinatePurityInput.pairArrow (OpenRing A V x I) I (coordinate A V x I) G) ≫
          DerivedCategory.Q.map ((G.map (punctureIso A V x I).hom)⟦(1 : ℤ)⟧') :=
  ConeDerivedComparison.coneIso_boundary _ _ _ _ _

variable (Allowed : Finset V → Prop) (r : ℕ) (i : PrimeLayerCover.Index Allowed r)

def layerIso :
    CoordinatePurityInput.relative (OpenRing A V x i.val) i.val (coordinate A V x i.val) G ≅
      PrimeLayerExcision.localRelative A V x Allowed G r i := by
  rcases i with ⟨J,hcard,hJ⟩
  subst r
  exact relativeIso A V x J G

#print axioms localArrow
#print axioms pair_square
#print axioms relativeIso
#print axioms relativeIso_boundary
#print axioms layerIso
end Verification.PrimeLocalCone
