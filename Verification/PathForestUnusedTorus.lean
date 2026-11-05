/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestPartitionPresentation
import Verification.EmptyNestedExchange
import Verification.TorusContractedModel

/-!
# Path Forest Unused Torus

The unused frozen factor of the actual normalized path forest is its
literal split torus. Both its smoothness and its contracted strict model
are transported through that proved algebra isomorphism.
-/
noncomputable section
namespace Verification.PathForestUnusedTorus
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.ContractedStrictProductInput
open Verification.PathForestFrozenPartition Verification.PathForestPartitionPresentation
variable {S F : Type} [Fintype S] [Fintype F] (m : S→ℕ) (o : S→Bool)
variable (R : Type) [CommRing R]

def algebraEquiv : Factor (F:=F) m o R none ≃ₐ[R]
    LaurentScalarModel.Coefficients R (Unused (F:=F) o→ℤ) := by
  letI : IsEmpty (Vertex m o none) := inferInstanceAs (IsEmpty Empty)
  exact EmptyNestedExchange.equiv R (Coefficient (F:=F) o R none) (branchPolynomial (F:=F) m o R none)

def smooth : Algebra.Smooth R (Factor (F:=F) m o R none) := by
  letI := TorusContractedModel.functionSmooth R (Unused (F:=F) o)
  exact Algebra.Smooth.of_equiv (algebraEquiv (F:=F) m o R).symm

universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ,(CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (empty : ∀ X : Scheme,IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))

def model : ContractedModel J
    (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (Factor (F:=F) m o R none))))))
    (T.cell Empty Empty (Unused (F:=F) o)).term :=
  ContractedModelTransport.ring J L G (algebraEquiv (F:=F) m o R).toRingEquiv
    (TorusContractedModel.functionModel J L G R T empty (Unused (F:=F) o))

#print axioms algebraEquiv
#print axioms smooth
#print axioms model
end Verification.PathForestUnusedTorus
