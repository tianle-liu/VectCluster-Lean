/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WeightedConstantTerms
import Verification.PathGradedSheafModel
import Verification.PathZeroWeightIndex

/-!
# Path Normal Term Iso

Exact term isomorphisms from all normal words, including the unique
constant word, to the positive path realization with its constant complex.
-/
noncomputable section
namespace Verification.PathNormalTermIso
open Classical CategoryTheory CategoryTheory.Limits
open Verification.PathWeightFiltration Verification.PathStratumGrading
open Verification.PathNormalizedBasis Verification.PathEndpointWords
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C] [HasZeroObject C]
variable (Z : C) (K : ℕ → C)
variable (A : PathGradedCoefficientAction.Action (fun j=>K (j+1)))

def y (a : ℕ) (p : ℤ) :
    (⨁ fun i : {i : NormalIndex BothNormal (2*a) // -degree i=p} =>
      if weight i.val=0 then Z else K (weight i.val)) ≅
    (PathGradedSheafModel.ySource K A Z a).X p :=
  WeightedConstantTerms.realizationIso weight (fun i=>-degree i) Z K
    (PathZeroWeightIndex.yIndex a) (PathZeroWeightIndex.yIndex_weight a)
    (PathZeroWeightIndex.yIndex_degree a) (PathZeroWeightIndex.y_unique a)
    A (PathPositiveContraction.yData a) p

def z (n : ℕ) (p : ℤ) :
    (⨁ fun i : {i : NormalIndex RightNormal n // -degree i=p} =>
      if weight i.val=0 then Z else K (weight i.val)) ≅
    (PathGradedSheafModel.zSource K A Z n).X p :=
  WeightedConstantTerms.realizationIso weight (fun i=>-degree i) Z K
    (PathZeroWeightIndex.zIndex n) (PathZeroWeightIndex.zIndex_weight n)
    (PathZeroWeightIndex.zIndex_degree n) (PathZeroWeightIndex.z_unique n)
    A (PathPositiveContraction.zData n) p

#print axioms y
#print axioms z
end Verification.PathNormalTermIso
