/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedLineContraction
import Verification.LocalizedPrincipalPurity
import Verification.LaurentBasepoint
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Standard Line Thom Contraction

The canonical localized boundary of the standard (A1,Gm) pair over any
smooth algebra. Its cone is the shifted kernel of the actual u=1 retraction.
These constructions contain no exchange matrix or stratification.
-/
noncomputable section
namespace Verification.StandardLineThomContraction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite CochainComplex
universe u w
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
variable (L : DerivedCategory C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ)

def openArrow := PrincipalPurityInterface.restriction R F (Polynomial A) Polynomial.X

def lineProjection := F.map (IsScalarTower.toAlgHom R A (Polynomial A)).toUnder.op

omit [HasDerivedCategory C] [HasBinaryBiproducts C] in
theorem line_square : openArrow R A F ≫ lineProjection R A F =
    (𝟙 _) ≫ LaurentBasepoint.projection R A F := by
  unfold openArrow PrincipalPurityInterface.restriction lineProjection LaurentBasepoint.projection
  rw [Category.id_comp, ← Functor.map_comp]
  rfl

variable [IsIso (L.map (DerivedCategory.Q.map (lineProjection R A F)))]

def lineConeIso :
    L.obj (DerivedCategory.Q.obj (mappingCone (openArrow R A F))) ≅
    L.obj (DerivedCategory.Q.obj (mappingCone (LaurentBasepoint.projection R A F))) := by
  letI : IsIso (L.map (DerivedCategory.Q.map (𝟙 (F.obj (op (CommRingCat.mkUnder
      (CommRingCat.of R) (LaurentBasepoint.Laurent A))))))) := by
    simp only [CategoryTheory.Functor.map_id]
    infer_instance
  exact LocalizedConeComparison.coneIso L _ _ (𝟙 _) (lineProjection R A F) (line_square R A F)

theorem lineConeIso_boundary : (lineConeIso R A L F).hom ≫
    L.map (TransverseDerivedBoundary.boundary (LaurentBasepoint.projection R A F)) =
    L.map (TransverseDerivedBoundary.boundary (openArrow R A F)) := by
  have h := TransverseDerivedBoundary.boundary_naturality
    (openArrow R A F) (LaurentBasepoint.projection R A F)
    (𝟙 _) (lineProjection R A F) (line_square R A F)
  simpa only [Functor.map_comp, CategoryTheory.Functor.map_id, Category.comp_id] using congrArg L.map h

def contractionIso :
    L.obj (DerivedCategory.Q.obj (mappingCone (openArrow R A F))) ≅
    L.obj (DerivedCategory.Q.obj ((kernel (LaurentBasepoint.projection R A F))⟦(1 : ℤ)⟧)) :=
  lineConeIso R A L F ≪≫ L.mapIso (SplitEpiConeKernel.splitConeKernelIso
    (LaurentBasepoint.projection R A F) (LaurentBasepoint.sectionMap R A F)
    (LaurentBasepoint.section_projection R A F))

theorem contractionIso_boundary : (contractionIso R A L F).hom ≫
    L.map (DerivedCategory.Q.map ((kernel.ι (LaurentBasepoint.projection R A F))⟦(1 : ℤ)⟧')) =
    L.map (TransverseDerivedBoundary.boundary (openArrow R A F)) := by
  simp only [contractionIso, Iso.trans_hom, Category.assoc, Functor.mapIso_hom, ← Functor.map_comp,
    SplitEpiConeKernel.split_positive_boundary]
  exact lineConeIso_boundary R A L F

def closedEquiv : PrincipalPairMaps.Closed (Polynomial A) Polynomial.X ≃ₐ[R] A :=
  ((Ideal.quotientEquivAlgOfEq A
    (show Ideal.span {(Polynomial.X : Polynomial A)} =
      Ideal.span {Polynomial.X - Polynomial.C (0 : A)} by simp only [map_zero, sub_zero])).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (0 : A))).restrictScalars R

variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ D)
variable (P : LocalizedPrincipalPurity.Standard L R F T) [Algebra.Smooth R A]

def sliceIso : T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) A)) ≅
    L.obj (DerivedCategory.Q.obj (mappingCone (openArrow R A F))) := by
  letI : Algebra.Smooth A (Polynomial A) := {}
  letI : Algebra.Smooth R (Polynomial A) := Algebra.Smooth.comp R A (Polynomial A)
  exact T.mapIso (closedEquiv R A).toUnder.op ≪≫
    P.comparison (Polynomial A) Polynomial.X inferInstance
      (Algebra.Smooth.of_equiv (closedEquiv R A).symm) Polynomial.isRegular_X.left

def thomIso : T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) A)) ≅
    L.obj (DerivedCategory.Q.obj ((kernel (LaurentBasepoint.projection R A F))⟦(1 : ℤ)⟧)) :=
  sliceIso R A L F T P ≪≫ contractionIso R A L F

theorem thomIso_boundary : (thomIso R A L F T P).hom ≫
    L.map (DerivedCategory.Q.map ((kernel.ι (LaurentBasepoint.projection R A F))⟦(1 : ℤ)⟧')) =
    (sliceIso R A L F T P).hom ≫ L.map (TransverseDerivedBoundary.boundary (openArrow R A F)) := by
  simp only [thomIso, Iso.trans_hom, Category.assoc, contractionIso_boundary]

#print axioms openArrow
#print axioms lineProjection
#print axioms line_square
#print axioms lineConeIso
#print axioms lineConeIso_boundary
#print axioms contractionIso
#print axioms contractionIso_boundary
#print axioms closedEquiv
#print axioms sliceIso
#print axioms thomIso
#print axioms thomIso_boundary
end Verification.StandardLineThomContraction
