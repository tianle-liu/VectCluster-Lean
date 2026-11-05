/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestZeroWeight
import Verification.BiproductMultiplicity
import Verification.WeightedMilnorWittTensor

/-!
# Path Forest Weight Multiplicity

The coefficients of the manuscript's polynomial are the literal
multiplicities of the actual finite weighted sum, with one integer summand.
-/
noncomputable section
namespace Verification.PathForestWeightMultiplicity
open Classical CategoryTheory CategoryTheory.Limits
open Verification.PathForestWeightPolynomial Verification.WeightedMilnorWittTensor
attribute [local instance] Abelian.hasFiniteBiproducts
variable {S : Type} [Fintype S] (U : Type) [Fintype U] (m : S→ℕ) (o : S→Bool)

theorem coefficient (j : ℕ) : FiniteMultiplicity.multiplicity (weight U m o) j=
    (paperPolynomial U m o).coeff j := by
  rw [coefficient_count,FiniteMultiplicity.multiplicity]
  exact Fintype.card_subtype _

variable {A : Type*} [Category A] [Abelian A] (Z : A) (M : ℤ→A)

def groupedIso : (⨁ fun a : Choices U m o=>object Z M (weight U m o a)) ≅
    ⨁ fun j : Set.range (weight U m o)=>
      ⨁ fun _ : Fin ((paperPolynomial U m o).coeff j.val)=>object Z M j.val :=
  BiproductMultiplicity.groupedIso (weight U m o) (object Z M) ≪≫
    biproduct.mapIso (fun j=>biproduct.whiskerEquiv
      (f:=fun _ : Fin (FiniteMultiplicity.multiplicity (weight U m o) j.val)=>object Z M j.val)
      (g:=fun _ : Fin ((paperPolynomial U m o).coeff j.val)=>object Z M j.val)
      (finCongr (coefficient U m o j.val)) (fun _=>Iso.refl _))

def zeroIso : (⨁ fun _ : Fin ((paperPolynomial U m o).coeff 0)=>Z) ≅ Z :=
  biproduct.whiskerEquiv
    (f:=fun _ : Fin ((paperPolynomial U m o).coeff 0)=>Z)
    (g:=fun _ : Fin 1=>Z)
    (finCongr (PathForestZeroWeight.constant_coefficient U m o)) (fun _=>Iso.refl _) ≪≫
    biproductUniqueIso (fun _ : Fin 1=>Z)

#print axioms coefficient
#print axioms groupedIso
#print axioms zeroIso
end Verification.PathForestWeightMultiplicity
