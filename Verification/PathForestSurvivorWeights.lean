/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestContractedModel
import Verification.PathWeightBiproduct
import Verification.TorusWeightedSurvivors
import Verification.FiniteWeightedFamily
import Verification.FiniteMonoidalProductCongr

/-!
# Path Forest Survivor Weights

The degree-zero survivor of the actual standard forest contraction is
exactly the sum over the manuscript's weighted choices, including its true
integer coefficient object at weight zero.
-/
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 150000
namespace Verification.PathForestSurvivorWeights
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Verification.PathForestFrozenPartition Verification.PathForestWeightPolynomial
open Verification.WeightedMilnorWittTensor
open scoped BigOperators
attribute [local instance] Abelian.hasFiniteBiproducts
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [HasBinaryBiproducts A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ) (R : Type) [Field R]
variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (Z : A) (M : ℤ→A)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ→Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (Symbols : StrictTorusSymbolInput.Standard J L G R T Z M site N W V)
variable {S F : Type} [Fintype S] [Fintype F] (m : S→ℕ) (o : S→Bool)

def factorIso (j : Option S) :
    PathForestContractedModel.factorSurvivor J L G R M T Z (F:=F) m o j ≅
    ⨁ fun a : Choice (Unused (F:=F) o) m o j=>
      object Z M (factorWeight (Unused (F:=F) o) m o j a) := by
  cases j with
  | none=>exact TorusWeightedSurvivors.iso J L G R T Z M site N W V Symbols (Unused (F:=F) o)
  | some s=>
    change (if o s=true then Z ⊞ ⨁ fun k : Fin (2*m s+1+1)=>M ((k.val+1:ℕ):ℤ)
      else Z ⊞ ⨁ fun k : Fin (m s)=>M ((2*(k.val+1):ℕ):ℤ)) ≅
      ⨁ fun a : Branch (m s) (o s)=>object Z M (branchWeight (m s) (o s) a)
    generalize h : o s=b
    cases b
    · exact PathWeightBiproduct.even Z M (m s)
    · exact PathWeightBiproduct.odd Z M (m s)

variable [MonoidalCategory A] [MonoidalPreadditive A]
variable (unit : Z≅𝟙_ A) (MW : PositiveMilnorWittTensorInput.Standard M)

def iso : FiniteContractedProduct.survivors
    (Z⊞⨁ fun k : Fin 0=>M ((2*(k.val+1):ℕ):ℤ)) (Fintype.card (Option S))
    (fun j=>PathForestContractedModel.factorSurvivor J L G R M T Z (F:=F) m o
      ((Fintype.equivFin (Option S)).symm j)) ≅
    ⨁ fun a : Choices (Unused (F:=F) o) m o=>object Z M (weight (Unused (F:=F) o) m o a) :=
  FiniteMonoidalProductCongr.iso (PathWeightBiproduct.emptyBase Z M) (Fintype.card (Option S)) _ _
    (fun j=>factorIso J L G R T Z M site N W V Symbols m o ((Fintype.equivFin (Option S)).symm j)) ≪≫
      FiniteWeightedFamily.iso (Choice (Unused (F:=F) o) m o)
        (factorWeight (Unused (F:=F) o) m o) Z M unit MW

#print axioms factorIso
#print axioms iso
end Verification.PathForestSurvivorWeights
