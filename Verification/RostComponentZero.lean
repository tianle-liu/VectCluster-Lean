/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostWeightZero
import Verification.RostFiniteProducts
import Verification.DomainProductComponents

/-!
# Rost Component Zero

Weight-zero cycle sections on an actual finite product of domains
are integer functions on its genuine connected components. The product
decomposition is given as a ring isomorphism, not as an identification
of a formal component label with a geometric component.
-/
noncomputable section
namespace Verification.RostComponentZero
open CategoryTheory AlgebraicGeometry
variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (Z : RostWeightZero.IntegralConvention T)
variable {J : Type} [Fintype J] (R : J→Type) [∀ j,CommRing (R j)] [∀ j,IsDomain (R j)]
variable {A : Type} [CommRing A] (e : A≃+*∀ j,R j)

def indexFunctions : (J→ℤ) ≃+ (ConnectedComponents (PrimeSpectrum A)→ℤ) where
  toFun f c := f (DomainProductComponents.transport R e c)
  invFun f j := f ((DomainProductComponents.transport R e).symm j)
  left_inv f := by funext j; simp
  right_inv f := by funext c; simp
  map_add' _ _ := rfl

def componentIso : (T.cycles (Spec (CommRingCat.of A)) 0).homology 0 ≅
    AddCommGrp.of (ConnectedComponents (PrimeSpectrum A)→ℤ) :=
  T.iso (Scheme.Spec.mapIso e.toCommRingCatIso.symm.op) 0 0 ≪≫
    (F.product J R 0 0).toAddCommGrpIso ≪≫
    (AddEquiv.piCongrRight (fun j => (Z.zero (R j)).addCommGroupIsoToAddEquiv)).toAddCommGrpIso
      (X := AddCommGrp.of (∀ j,(T.cycles (Spec (CommRingCat.of (R j))) 0).homology 0))
      (Y := AddCommGrp.of (J→ℤ)) ≪≫
    (indexFunctions R e).toAddCommGrpIso (X := AddCommGrp.of (J→ℤ))

#print axioms indexFunctions
#print axioms componentIso
end Verification.RostComponentZero
