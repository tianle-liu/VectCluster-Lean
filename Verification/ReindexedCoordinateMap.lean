/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePurityNaturality
import Verification.CoordinatePairReindex

/-!
# Reindexed Coordinate Map

Actual maps of framed coordinate pairs with a bijection of the normal
index sets. Both the quotient map and the normal polynomial map are
constructed from the given ring map and its literal coordinate identities.
-/
noncomputable section
namespace Verification.ReindexedCoordinateMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.CoordinatePurityInput
universe w
variable {A B ι κ : Type} [CommRing A] [CommRing B]
variable (x : ι → A) (y : κ → B) (e : κ ≃ ι)
variable (f : A →+* B) (hf : ∀ i,f (x (e i)) = y i)

include hf in
theorem ideal_map : Ideal.map f (ConormalFrame.ideal x) ≤ ConormalFrame.ideal y := by
  rw [ConormalFrame.ideal,Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨a,⟨i,rfl⟩,rfl⟩
  have hi : f (x i) = y (e.symm i) := by simpa using hf (e.symm i)
  rw [hi]
  exact Ideal.subset_span ⟨e.symm i,rfl⟩

def closedMap : A ⧸ ConormalFrame.ideal x →+* B ⧸ ConormalFrame.ideal y :=
  Ideal.quotientMap _ f ((Ideal.map_le_iff_le_comap).mp (ideal_map x y e f hf))

theorem closedMap_mk (a : A) : closedMap x y e f hf (Ideal.Quotient.mk _ a) =
    Ideal.Quotient.mk _ (f a) := rfl

def normalPolynomialMap : MvPolynomial ι (A ⧸ ConormalFrame.ideal x) →+*
    MvPolynomial κ (B ⧸ ConormalFrame.ideal y) :=
  (MvPolynomial.rename e.symm).toRingHom.comp (MvPolynomial.map (closedMap x y e f hf))

theorem normalPolynomialMap_X (i : κ) :
    normalPolynomialMap x y e f hf (MvPolynomial.X (e i)) = MvPolynomial.X i := by
  simp [normalPolynomialMap]

theorem normalPolynomialMap_C (a : A ⧸ ConormalFrame.ideal x) :
    normalPolynomialMap x y e f hf (MvPolynomial.C a) = MvPolynomial.C (closedMap x y e f hf a) := by
  simp [normalPolynomialMap]

variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def relativeMap : relative B κ y G ⟶ relative A ι x G :=
  CoordinatePairMap.relativeMap (x ∘ e) y f hf G ≫
    (CoordinatePairReindex.relativeIso A ι κ x e G).inv

def normalMap : normalThom B κ y G ⟶ normalThom A ι x G :=
  CoordinatePairMap.relativeMap (MvPolynomial.X ∘ e) MvPolynomial.X
    (normalPolynomialMap x y e f hf) (normalPolynomialMap_X x y e f hf) G ≫
      (CoordinatePairReindex.relativeIso (MvPolynomial ι (A ⧸ ConormalFrame.ideal x))
        ι κ MvPolynomial.X e G).inv

#print axioms ideal_map
#print axioms closedMap
#print axioms closedMap_mk
#print axioms normalPolynomialMap
#print axioms normalPolynomialMap_X
#print axioms normalPolynomialMap_C
#print axioms relativeMap
#print axioms normalMap
end Verification.ReindexedCoordinateMap
