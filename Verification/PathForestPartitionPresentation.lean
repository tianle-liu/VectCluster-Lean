/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestFrozenPartition
import Verification.PartitionedExchangeTensor
import Verification.NestedExchangeCoordinateEquiv
import Verification.ActualPathForestStandard

/-!
# Path Forest Partition Presentation

The actual normalized forest algebra is a finite tensor over the ground
ring of separate path presentations and one unused Laurent coefficient factor.
-/
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.PathForestPartitionPresentation
open Classical MvPolynomial
open Verification.PathForestQuotient Verification.PathForestFrozenBasis
open Verification.PathForestFrozenPartition Verification.PathForestComponentMatrix
open scoped TensorProduct
variable {S F : Type} [Fintype S] [Fintype F] (m : S → ℕ) (o : S → Bool)

def Vertex : Option S → Type
  | none => Empty
  | some s => Fin (PathOrientationBlocks.length (m s) (o s))

instance vertexFintype (j : Option S) : Fintype (Vertex m o j) := by
  cases j <;> dsimp [Vertex] <;> infer_instance

def index : PathForestOrientation.Vertex m o ≃ Sigma (Vertex m o) where
  toFun v := ⟨some v.1,v.2⟩
  invFun v := match v with
    | ⟨none,i⟩ => nomatch i
    | ⟨some s,i⟩ => ⟨s,i⟩
  left_inv _ := rfl
  right_inv v := by rcases v with ⟨_|s,i⟩;cases i;rfl

variable (R : Type) [CommRing R]
abbrev Coefficient (j : Option S) := FiniteGroupAlgebraTensor.Factor R (Lattice (F:=F) o) j

def branchPolynomial (j : Option S) : Vertex m o j → MvPolynomial (Vertex m o j) (Coefficient (F:=F) o R j) :=
  match j with
  | none => fun i=>nomatch i
  | some s => LaurentScalarModel.exchange R
      (PathLattice.pathMatrix (PathOrientationBlocks.length (m s) (o s)))
      (endpointColumn (F:=F) o m s) (fun _=>1)

def sourceColumn (v : PathForestOrientation.Vertex m o) : NewFrozen (F:=F) o → ℤ :=
  fun a=>standardFrozen (F:=F) m o a ((PathForestOrientation.reindex m o).symm v)

def sourcePolynomial : PathForestOrientation.Vertex m o →
    MvPolynomial (PathForestOrientation.Vertex m o) (LaurentScalarModel.Coefficients R (NewFrozen (F:=F) o → ℤ)) :=
  LaurentScalarModel.exchange R (PathForestComponentPresentation.blockMatrix m o)
    (sourceColumn (F:=F) m o) (fun _=>1)

abbrev Source := NestedExchangeUniversal.Ring
  (LaurentScalarModel.Coefficients R (NewFrozen (F:=F) o → ℤ)) (sourcePolynomial (F:=F) m o R)
abbrev Factor (j : Option S) := NestedExchangeUniversal.Ring
  (Coefficient (F:=F) o R j) (branchPolynomial (F:=F) m o R j)
abbrev Product := ⨂[R] j,Factor (F:=F) m o R j

theorem polynomial_eq : NestedExchangeCoordinateEquiv.transported R (index m o)
    (coefficientEquiv (F:=F) o R) (sourcePolynomial (F:=F) m o R)=
    PartitionedExchangeTensor.polynomial R (Coefficient (F:=F) o R) (Vertex m o)
      (branchPolynomial (F:=F) m o R) := by
  funext v
  rcases v with ⟨_|s,i⟩
  · cases i
  · change NestedExchangeCoordinateEquiv.polynomial R (index m o) (coefficientEquiv (F:=F) o R)
      (sourcePolynomial (F:=F) m o R ⟨s,i⟩)=
      PartitionedExchangeTensor.embed R (Coefficient (F:=F) o R) (Vertex m o) (some s)
        (branchPolynomial (F:=F) m o R (some s) i)
    rw [show sourcePolynomial (F:=F) m o R ⟨s,i⟩=
      rename (Sigma.mk s) (LaurentScalarModel.exchange R
        (PathLattice.pathMatrix (PathOrientationBlocks.length (m s) (o s)))
        (fun i=>sourceColumn (F:=F) m o ⟨s,i⟩) (fun _=>1) i) from
      LaurentExchangeComponents.exchange_block R
        (fun s=>Fin (PathOrientationBlocks.length (m s) (o s)))
        (fun s=>PathLattice.pathMatrix (PathOrientationBlocks.length (m s) (o s)))
        (fun s i=>sourceColumn (F:=F) m o ⟨s,i⟩) (fun _ _=>1) ⟨s,i⟩]
    simp only [branchPolynomial,LaurentScalarModel.exchange,map_add,map_mul,map_prod,map_pow,
      rename_C,rename_X,NestedExchangeCoordinateEquiv.polynomial_C,
      NestedExchangeCoordinateEquiv.polynomial_X,Units.val_one,map_one,one_mul,
      PartitionedExchangeTensor.embed,aevalTower_C,aevalTower_X,AlgHom.comp_apply,
      IsScalarTower.toAlgHom_apply,MvPolynomial.algebraMap_eq]
    rw [show coefficientEquiv (F:=F) o R (ExchangeCharacters.monomial
        (sourceColumn (F:=F) m o ⟨s,i⟩))=
      PiTensorProduct.singleAlgHom (some s) (ExchangeCharacters.monomial
        (endpointColumn (F:=F) o m s i)) from coefficient_column (F:=F) o m R s i]
    have hd : @PiTensorProduct.singleAlgHom (Option S) R (Coefficient (F:=F) o R)
        _ _ _ (inferInstance : DecidableEq (Option S)) (some s)=
      @PiTensorProduct.singleAlgHom (Option S) R (Coefficient (F:=F) o R)
        _ _ _ (fun a b=>Classical.propDecidable (a=b)) (some s) :=
      congrArg (fun d : DecidableEq (Option S)=>
        @PiTensorProduct.singleAlgHom (Option S) R (Coefficient (F:=F) o R) _ _ _ d (some s))
        (Subsingleton.elim _ _)
    rw [hd]
    rfl

def equivalence : Source (F:=F) m o R ≃ₐ[R] Product (F:=F) m o R :=
  (NestedExchangeCoordinateEquiv.equiv R (index m o) (coefficientEquiv (F:=F) o R)
      (sourcePolynomial (F:=F) m o R)).trans
    ((Ideal.quotientEquivAlgOfEq R (congrArg (fun p=>PartnerScaling.relations (fun i=>X i) p)
      (polynomial_eq (F:=F) m o R))).trans
      (PartitionedExchangeTensor.equivalence R (Coefficient (F:=F) o R) (Vertex m o)
        (branchPolynomial (F:=F) m o R)))

variable (n : ℕ) (e : PathForestComponentMatrix.Vertices m o ≃ Fin n)
variable (B : Matrix (Fin n ⊕ F) (Fin n ⊕ Empty) ℤ)
variable (hprincipal : ∀ i j,B (Sum.inl (e i)) (Sum.inl (e j))=ordinaryMatrix m o i j)
variable (hAS : ∀ I,ExchangeReindex.PrincipalIndependent (EmptyColumnRetraction.cut B) I →
  AnticliqueSubcolumns.AS (EmptyColumnRetraction.cut B) I)

def originalEquiv : FrozenAcyclicCover.Global R F n B ≃ₐ[R] Product (F:=F) m o R :=
  (ActualPathForestStandard.originalEquiv R m o n e B hprincipal hAS).trans
    ((PathForestComponentPresentation.consecutiveEquiv m o R
      (LaurentRowCorrection.column (standardFrozen (F:=F) m o)) (fun _=>1)).trans
        (equivalence (F:=F) m o R))

#print axioms Vertex
#print axioms vertexFintype
#print axioms index
#print axioms Coefficient
#print axioms branchPolynomial
#print axioms sourceColumn
#print axioms sourcePolynomial
#print axioms Source
#print axioms Factor
#print axioms Product
#print axioms polynomial_eq
#print axioms equivalence
#print axioms originalEquiv
end Verification.PathForestPartitionPresentation
