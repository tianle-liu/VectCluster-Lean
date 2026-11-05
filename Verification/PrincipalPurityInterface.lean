/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrincipalPairMaps
import Verification.TransverseDerivedBoundary
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.RingTheory.Smooth.Basic

/-!
# Principal Purity Interface

A uniform external interface for the cited natural homotopy-purity
theorem for smooth principal pairs. The interface concerns Thom/cofiber
identification for arbitrary parameter-preserving transverse maps. It does
not postulate a cellular differential or a torus residue formula.
-/
namespace Verification.PrincipalPurityInterface
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.PrincipalPairMaps
universe u w
variable (R : Type u) [CommRing R]
variable {D : Type*} [Category D] [Abelian D] [HasBinaryBiproducts D] [HasDerivedCategory.{w} D]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex D ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ DerivedCategory D)

noncomputable def restriction (A : Type u) [CommRing A] [Algebra R A] (a : A) :
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Open A a))) ⟶
      F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) A)) :=
  F.map (IsScalarTower.toAlgHom R A (Open A a)).toUnder.op

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable (a : A) (b : B) (φ : A →ₐ[R] B) (h : φ a = b)

omit [HasBinaryBiproducts D] [HasDerivedCategory D] in
theorem pair_square : restriction R F B b ≫ F.map φ.toUnder.op =
    F.map (openMap R A B a b φ h).toUnder.op ≫ restriction R F A a := by
  have hs := congrArg (fun f : A →ₐ[R] Open B b => F.map f.toUnder.op)
    (open_square R A B a b φ h).symm
  unfold restriction
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact hs

noncomputable def pairConeMap :
    DerivedCategory.Q.obj (mappingCone (restriction R F B b)) ⟶
      DerivedCategory.Q.obj (mappingCone (restriction R F A a)) :=
  DerivedCategory.Q.map (TransverseConeBoundary.coneMap _ _
    (F.map (openMap R A B a b φ h).toUnder.op) (F.map φ.toUnder.op)
    (pair_square R F A B a b φ h))

noncomputable def closedTheoryMap :
    T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Closed B b))) ⟶
      T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Closed A a))) :=
  T.map (closedMap R A B a b φ h).toUnder.op

abbrev Comparison := Arrow.mk (closedTheoryMap R T A B a b φ h) ≅
  Arrow.mk (pairConeMap R F A B a b φ h)

/-- The cited theorem is supplied uniformly for smooth principal pairs.
All hypotheses concern actual rings, actual principal quotients, and the
literal parameter identity; none is a desired differential equality. -/
structure StandardPurity where
  comparison : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (a : A) (b : B) (φ : A →ₐ[R] B) (h : φ a = b),
    Algebra.Smooth R A → Algebra.Smooth R (Closed A a) →
    Algebra.Smooth R B → Algebra.Smooth R (Closed B b) →
    IsSMulRegular A a → IsSMulRegular B b → Comparison R F T A B a b φ h

#print axioms restriction
#print axioms pair_square
#print axioms pairConeMap
#print axioms closedTheoryMap
#print axioms Comparison
#print axioms StandardPurity
end Verification.PrincipalPurityInterface
