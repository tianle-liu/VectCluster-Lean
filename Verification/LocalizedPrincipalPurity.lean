/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrincipalObjectPurity

/-!
# Localized Principal Purity

Principal homotopy purity in the localized ambient category. One fixed
comparison is assigned to each genuine smooth regular pair; its ordinary
transverse naturality implies boundary naturality after L.
-/
noncomputable section
namespace Verification.LocalizedPrincipalPurity
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.PrincipalPairMaps
universe u w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D]
variable (L : DerivedCategory C ⥤ D)
variable (R : Type u) [CommRing R]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ D)

structure Standard where
  comparison : ∀ (A : Type u) [CommRing A] [Algebra R A] (a : A),
    Algebra.Smooth R A → Algebra.Smooth R (Closed A a) → IsSMulRegular A a →
      (T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Closed A a))) ≅
        L.obj (DerivedCategory.Q.obj (mappingCone (PrincipalPurityInterface.restriction R F A a))))
  naturality : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (a : A) (b : B) (φ : A →ₐ[R] B) (h : φ a = b)
    (hA : Algebra.Smooth R A) (hAc : Algebra.Smooth R (Closed A a))
    (hB : Algebra.Smooth R B) (hBc : Algebra.Smooth R (Closed B b))
    (ha : IsSMulRegular A a) (hb : IsSMulRegular B b),
    T.map (closedMap R A B a b φ h).toUnder.op ≫ (comparison A a hA hAc ha).hom =
      (comparison B b hB hBc hb).hom ≫ L.map (PrincipalPurityInterface.pairConeMap R F A B a b φ h)

variable (P : Standard L R F T)
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable (a : A) (b : B) (φ : A →ₐ[R] B) (h : φ a = b)
variable (hA : Algebra.Smooth R A) (hAc : Algebra.Smooth R (Closed A a))
variable (hB : Algebra.Smooth R B) (hBc : Algebra.Smooth R (Closed B b))
variable (ha : IsSMulRegular A a) (hb : IsSMulRegular B b)

def arrowPurity : Arrow.mk (T.map (closedMap R A B a b φ h).toUnder.op) ≅
    Arrow.mk (L.map (PrincipalPurityInterface.pairConeMap R F A B a b φ h)) :=
  Arrow.isoMk (P.comparison B b hB hBc hb) (P.comparison A a hA hAc ha)
    (P.naturality A B a b φ h hA hAc hB hBc ha hb).symm

theorem boundary_naturality : T.map (closedMap R A B a b φ h).toUnder.op ≫
    (P.comparison A a hA hAc ha).hom ≫
      L.map (TransverseDerivedBoundary.boundary (PrincipalPurityInterface.restriction R F A a)) =
    (P.comparison B b hB hBc hb).hom ≫
      L.map (TransverseDerivedBoundary.boundary (PrincipalPurityInterface.restriction R F B b)) ≫
        L.map (DerivedCategory.Q.map ((F.map (openMap R A B a b φ h).toUnder.op)⟦(1 : ℤ)⟧')) := by
  rw [← Category.assoc, P.naturality A B a b φ h hA hAc hB hBc ha hb, Category.assoc,
    ← Functor.map_comp]
  have hn := TransverseDerivedBoundary.boundary_naturality
    (PrincipalPurityInterface.restriction R F B b) (PrincipalPurityInterface.restriction R F A a)
    (F.map (openMap R A B a b φ h).toUnder.op) (F.map φ.toUnder.op)
    (PrincipalPurityInterface.pair_square R F A B a b φ h)
  change PrincipalPurityInterface.pairConeMap R F A B a b φ h ≫ _ = _ at hn
  rw [hn, Functor.map_comp]

#print axioms Standard
#print axioms arrowPurity
#print axioms boundary_naturality
end Verification.LocalizedPrincipalPurity
