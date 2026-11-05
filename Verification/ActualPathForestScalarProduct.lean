/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestPartitionPresentation

/-!
# Actual Path Forest Scalar Product

The scalar coefficient version of the genuine ground-ring tensor
factorization. Scalar units are removed by the already proved AS normalization.
-/
noncomputable section
namespace Verification.ActualPathForestScalarProduct
open Verification.PathForestComponentMatrix Verification.PathForestFrozenBasis
variable {S F : Type} [Fintype S] [Fintype F]
variable (R : Type) [CommRing R] (m : S → ℕ) (o : S → Bool)
variable (n : ℕ) (e : Vertices m o ≃ Fin n)
variable (B : Matrix (Fin n ⊕ F) (Fin n ⊕ Empty) ℤ)
variable (hprincipal : ∀ i j,B (Sum.inl (e i)) (Sum.inl (e j))=ordinaryMatrix m o i j)
variable (hAS : ∀ I,ExchangeReindex.PrincipalIndependent (EmptyColumnRetraction.cut B) I →
  AnticliqueSubcolumns.AS (EmptyColumnRetraction.cut B) I)

def scalarEquiv (a b : Fin n → Rˣ) : ScalarFrozenGlobal.Global R F n B a b ≃ₐ[R]
    PathForestPartitionPresentation.Product (F:=F) m o R :=
  (ActualPathForestStandard.standardEquiv R m o n e B hprincipal hAS a b).trans
    ((PathForestComponentPresentation.consecutiveEquiv m o R
      (LaurentRowCorrection.column (standardFrozen (F:=F) m o)) (fun _=>1)).trans
        (PathForestPartitionPresentation.equivalence (F:=F) m o R))

#print axioms scalarEquiv
end Verification.ActualPathForestScalarProduct
