/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ReindexedCoordinateMap
import Verification.ConeDerivedInverse
import Verification.LocalizedThomSections

/-!
# Reindexed Thom Map

The genuine normal-coordinate map for a coefficient homomorphism and
an index equivalence, expressed as its commuting square of schemes.
-/
noncomputable section
namespace Verification.ReindexedThomMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinatePurityInput
variable {S T ι κ : Type} [CommRing S] [CommRing T]
variable (e : κ ≃ ι) (f : S →+* T)

def polynomialMap : MvPolynomial ι S →+* MvPolynomial κ T :=
  (MvPolynomial.rename e.symm).toRingHom.comp (MvPolynomial.map f)

theorem coordinate (i : κ) : polynomialMap e f (MvPolynomial.X (e i))=MvPolynomial.X i := by
  simp [polynomialMap]

def openMap : (puncture (MvPolynomial κ T) κ MvPolynomial.X).toScheme ⟶
    (puncture (MvPolynomial ι S) ι MvPolynomial.X).toScheme :=
  CoordinatePairMap.punctureMap (MvPolynomial.X ∘ e) MvPolynomial.X
    (polynomialMap e f) (coordinate e f) ≫
      (CoordinatePairReindex.openIso (MvPolynomial ι S) ι κ MvPolynomial.X e).inv

theorem open_square : openMap e f ≫ (puncture (MvPolynomial ι S) ι MvPolynomial.X).ι =
    (puncture (MvPolynomial κ T) κ MvPolynomial.X).ι ≫
      Spec.map (CommRingCat.ofHom (polynomialMap e f)) := by
  have h : (CoordinatePairReindex.openIso (MvPolynomial ι S) ι κ MvPolynomial.X e).inv ≫
      (puncture (MvPolynomial ι S) ι MvPolynomial.X).ι =
        (puncture (MvPolynomial ι S) κ (MvPolynomial.X ∘ e)).ι := by
    apply (cancel_epi (CoordinatePairReindex.openIso (MvPolynomial ι S) ι κ MvPolynomial.X e).hom).mp
    rw [Iso.hom_inv_id_assoc,CoordinatePairReindex.open_square]
  rw [openMap,Category.assoc,h,← CoordinatePairMap.puncture_square]

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def map : LocalizedThomSections.thom G T κ ⟶ LocalizedThomSections.thom G S ι :=
  CoordinatePairMap.relativeMap (MvPolynomial.X ∘ e) MvPolynomial.X
    (polynomialMap e f) (coordinate e f) G ≫
      (CoordinatePairReindex.relativeIso (MvPolynomial ι S) ι κ MvPolynomial.X e G).inv

theorem cone_map : map e f G = TransverseDerivedBoundary.coneMap
    (pairArrow (MvPolynomial κ T) κ MvPolynomial.X G)
    (pairArrow (MvPolynomial ι S) ι MvPolynomial.X G)
    (G.map (openMap e f)) (G.map (Spec.map (CommRingCat.ofHom (polynomialMap e f))))
    (by simpa only [pairArrow,← Functor.map_comp] using congrArg G.map (open_square e f).symm) := by
  have h := ConeDerivedInverse.inverse
    (pairArrow (MvPolynomial ι S) ι MvPolynomial.X G)
    (pairArrow (MvPolynomial ι S) κ (MvPolynomial.X ∘ e) G)
    (G.mapIso (CoordinatePairReindex.openIso (MvPolynomial ι S) ι κ MvPolynomial.X e))
    (Iso.refl _) (CoordinatePairReindex.pair_square (MvPolynomial ι S) ι κ MvPolynomial.X e G)
  change (CoordinatePairReindex.relativeIso (MvPolynomial ι S) ι κ MvPolynomial.X e G).inv = _ at h
  simp only [map,h,Functor.mapIso_inv,Iso.refl_inv,CoordinatePairMap.relativeMap,
    TransverseDerivedBoundary.coneMap,TransverseConeBoundary.coneMap,
    ← Functor.map_comp,← mappingCone.map_comp,Category.comp_id,openMap]

variable {A B : Type} [CommRing A] [CommRing B]
variable (x : ι → A) (y : κ → B) (g : A →+* B) (hg : ∀ i,g (x (e i))=y i)

theorem actual_normal_map : ReindexedCoordinateMap.normalMap x y e g hg G =
    map e (ReindexedCoordinateMap.closedMap x y e g hg) G := rfl

#print axioms polynomialMap
#print axioms coordinate
#print axioms openMap
#print axioms open_square
#print axioms map
#print axioms cone_map
#print axioms actual_normal_map
end Verification.ReindexedThomMap
