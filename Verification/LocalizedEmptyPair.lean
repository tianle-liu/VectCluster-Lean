/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedConeComparison
import Verification.CoordinatePurityInput

/-!
# Localized Empty Pair

A coordinate pair with no normal coordinates has empty puncture.
Its genuine localized cone is consequently the ambient scheme object.
-/
noncomputable section
namespace Verification.LocalizedEmptyPair
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry CochainComplex
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ,(CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
variable (L : DerivedCategory C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (empty : ∀ X : Scheme,IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))
variable (S ι : Type) [CommRing S] [Fintype ι] [IsEmpty ι] (x : ι→S)

omit [Fintype ι] in
theorem puncture_empty : IsEmpty (CoordinatePurityInput.puncture S ι x).toScheme := by
  constructor
  intro p
  have hp := p.property
  simp [CoordinatePurityInput.puncture] at hp

def iso : L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of S)))) ≅
    L.obj (CoordinatePurityInput.relative S ι x G) := by
  let f := CoordinatePurityInput.pairArrow S ι x G
  let T := L.mapTriangle.obj (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle f))
  have hT : T ∈ distTriang D := L.map_distinguished _
    ((DerivedCategory.mem_distTriang_iff _).mpr ⟨_,_,f,⟨Iso.refl _⟩⟩)
  have h0 : IsZero T.obj₁ := empty _ (puncture_empty S ι x)
  letI : IsIso T.mor₂ := (Triangle.isZero₁_iff_isIso₂ T hT).mp h0
  exact asIso T.mor₂

#print axioms puncture_empty
#print axioms iso
end Verification.LocalizedEmptyPair
