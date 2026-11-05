/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteBiproductOption
import Verification.WeightedMilnorWittTensor
import Verification.PathForestWeightPolynomial

/-!
# Path Weight Biproduct

Literal minimal path survivors have the precise finite weight indices
used in the manuscript's generating polynomial.
-/
noncomputable section
namespace Verification.PathWeightBiproduct
open CategoryTheory CategoryTheory.Limits
open Verification.WeightedMilnorWittTensor Verification.PathForestWeightPolynomial
variable {A : Type*} [Category A] [Preadditive A] [HasFiniteBiproducts A] [HasBinaryBiproducts A]
variable (Z : A) (M : ℤ→A)

def even (a : ℕ) : (Z⊞⨁ fun k : Fin a=>M ((2*(k.val+1):ℕ):ℤ)) ≅
    ⨁ fun x : Branch a false=>object Z M (branchWeight a false x) :=
  FiniteBiproductOption.iso Z (fun k : Fin a=>M ((2*(k.val+1):ℕ):ℤ)) ≪≫
    biproduct.mapIso (fun x=>eqToIso (by
      cases x <;> simp [FiniteBiproductOption.family,branchWeight,object]))

def odd (a : ℕ) : (Z⊞⨁ fun k : Fin (2*a+1+1)=>M ((k.val+1:ℕ):ℤ)) ≅
    ⨁ fun x : Branch a true=>object Z M (branchWeight a true x) :=
  FiniteBiproductOption.iso Z (fun k : Fin (2*a+1+1)=>M ((k.val+1:ℕ):ℤ)) ≪≫
    biproduct.mapIso (fun x=>eqToIso (by
      cases x <;> simp [FiniteBiproductOption.family,branchWeight,object]))

def emptyBase : (Z⊞⨁ fun k : Fin 0=>M ((2*(k.val+1):ℕ):ℤ)) ≅ Z :=
  FiniteBiproductOption.iso Z (fun k : Fin 0=>M ((2*(k.val+1):ℕ):ℤ)) ≪≫
    biproductUniqueIso (FiniteBiproductOption.family Z (fun k : Fin 0=>M ((2*(k.val+1):ℕ):ℤ)))

#print axioms even
#print axioms odd
#print axioms emptyBase
end Verification.PathWeightBiproduct
