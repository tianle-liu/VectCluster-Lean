/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictTorusSymbolInput
import Verification.BinaryWeightCoordinates
import Verification.WeightedMilnorWittTensor

/-!
# Torus Weighted Survivors

The genuine torus cell's ordinary symbol splitting has exactly the
boolean coordinate choices and weights used in the forest polynomial.
-/
noncomputable section
namespace Verification.TorusWeightedSurvivors
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators
attribute [local instance] Abelian.hasFiniteBiproducts
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ) (R : Type) [CommRing R]
variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (Z : A) (M : ℤ→A)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ→Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (Symbols : StrictTorusSymbolInput.Standard J L G R T Z M site N W V)
variable (κ : Type) [Fintype κ] [LinearOrder κ]

def iso : (T.cell Empty Empty κ).term ≅
    ⨁ fun f : κ→Bool=>WeightedMilnorWittTensor.object Z M (∑u,FiniteWeightPolynomial.bitWeight (f u)) :=
  Symbols.split Empty Empty κ ≪≫
    biproduct.whiskerEquiv
      (f:=StrictTorusSymbolInput.summand Z M (Fintype.card Empty) (Fintype.card κ))
      (g:=fun f : κ→Bool=>WeightedMilnorWittTensor.object Z M (∑u,FiniteWeightPolynomial.bitWeight (f u)))
      (BinaryWeightCoordinates.equiv κ) (fun i=>eqToIso (by
        simp only [StrictTorusSymbolInput.summand,StrictTorusSymbolInput.degree,
          Fintype.card_empty,Nat.cast_zero,zero_add,BinaryWeightCoordinates.weight,
          WeightedMilnorWittTensor.object,Nat.cast_eq_zero]))

#print axioms iso
end Verification.TorusWeightedSurvivors
