/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteContractedProduct
import Verification.FiniteAlgebraReindex

/-!
# Finite Contracted Family

Finite products indexed by an arbitrary finite type inherit the genuine
contracted strict model. The index change is a proved algebra equivalence.
-/
noncomputable section
namespace Verification.FiniteContractedFamily
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped TensorProduct
open Verification.ContractedStrictProductInput
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [MonoidalCategory A] [MonoidalPreadditive A]
variable [Category C] [Abelian C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) (G : Scheme ⥤ CochainComplex C ℤ)
variable (k : Type) [Field k]
variable (MS : Standard J L G k)
variable {base : A}
variable (P₀ : ContractedModel J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of k))))) base)
variable (I : Type) [Fintype I]
variable (S : I→Type) [∀ i,CommRing (S i)] [∀ i,Algebra k (S i)] [∀ i,Algebra.Smooth k (S i)]
variable (U : I→A)
variable (P : ∀ i,ContractedModel J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (S i)))))) (U i))

def smooth : Algebra.Smooth k (⨂[k] i,S i) := by
  letI := FiniteAlgebraSmooth.finite k (Fintype.card I) (fun j=>S ((Fintype.equivFin I).symm j))
  exact Algebra.Smooth.of_equiv (FiniteAlgebraReindex.equiv k S (Fintype.equivFin I).symm)

def model : ContractedModel J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (⨂[k] i,S i))))))
    (FiniteContractedProduct.survivors base (Fintype.card I) (fun j=>U ((Fintype.equivFin I).symm j))) :=
  ContractedModelTransport.ring J L G (FiniteAlgebraReindex.equiv k S (Fintype.equivFin I).symm).symm.toRingEquiv
    (FiniteContractedProduct.model J L G k MS P₀ (Fintype.card I)
      (fun j=>S ((Fintype.equivFin I).symm j)) (fun j=>U ((Fintype.equivFin I).symm j))
      (fun j=>P ((Fintype.equivFin I).symm j)))

variable (Nis : StrictNisnevichInput.Theory A)
variable (NR : StrictNisnevichRepresentability.Standard J L G Nis k)
variable (HC : StrictCoefficientComparison.StandardHomology (A:=A))
include MS P₀ NR HC P in
omit [MonoidalPreadditive A] in
theorem vanishes (F : A) (p : ℕ) (hp : 0<p) :
    IsZero (Nis.cohomology (Spec (CommRingCat.of (⨂[k] i,S i))) F p) := by
  letI := smooth k I S
  exact ContractedStrictProductInput.vanishes J L G k (⨂[k] i,S i) Nis NR HC
    (model J L G k MS P₀ I S U P) F p hp

#print axioms smooth
#print axioms model
#print axioms vanishes
end Verification.FiniteContractedFamily
