/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrincipalPurityInterface

/-!
# Principal Object Purity

A coherent version of standard principal purity: each framed pair has
one fixed Thom comparison, and ordinary transverse pair maps commute with
those comparisons. It induces the existing arrow-purity interface.
-/
noncomputable section
namespace Verification.PrincipalObjectPurity
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.PrincipalPairMaps
universe u w
variable (R : Type u) [CommRing R]
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ DerivedCategory C)

structure Standard where
  comparison : ∀ (A : Type u) [CommRing A] [Algebra R A] (a : A),
    Algebra.Smooth R A → Algebra.Smooth R (Closed A a) → IsSMulRegular A a →
      (T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Closed A a))) ≅
        DerivedCategory.Q.obj (mappingCone (PrincipalPurityInterface.restriction R F A a)))
  naturality : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (a : A) (b : B) (φ : A →ₐ[R] B) (h : φ a = b)
    (hA : Algebra.Smooth R A) (hAc : Algebra.Smooth R (Closed A a))
    (hB : Algebra.Smooth R B) (hBc : Algebra.Smooth R (Closed B b))
    (ha : IsSMulRegular A a) (hb : IsSMulRegular B b),
    PrincipalPurityInterface.closedTheoryMap R T A B a b φ h ≫ (comparison A a hA hAc ha).hom =
      (comparison B b hB hBc hb).hom ≫ PrincipalPurityInterface.pairConeMap R F A B a b φ h

def arrowPurity (P : Standard R F T) : PrincipalPurityInterface.StandardPurity R F T where
  comparison A B _ _ _ _ a b φ h hA hAc hB hBc ha hb :=
    Arrow.isoMk (P.comparison B b hB hBc hb) (P.comparison A a hA hAc ha)
      (P.naturality A B a b φ h hA hAc hB hBc ha hb).symm

variable (P : Standard R F T)
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable (a : A) (b : B) (φ : A →ₐ[R] B) (h : φ a = b)
variable (hA : Algebra.Smooth R A) (hAc : Algebra.Smooth R (Closed A a))
variable (hB : Algebra.Smooth R B) (hBc : Algebra.Smooth R (Closed B b))
variable (ha : IsSMulRegular A a) (hb : IsSMulRegular B b)

theorem arrowPurity_left : ((arrowPurity R F T P).comparison A B a b φ h hA hAc hB hBc ha hb).hom.left =
    (P.comparison B b hB hBc hb).hom := rfl

theorem arrowPurity_right : ((arrowPurity R F T P).comparison A B a b φ h hA hAc hB hBc ha hb).hom.right =
    (P.comparison A a hA hAc ha).hom := rfl

#print axioms Standard
#print axioms arrowPurity
#print axioms arrowPurity_left
#print axioms arrowPurity_right
end Verification.PrincipalObjectPurity
