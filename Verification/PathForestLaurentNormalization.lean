/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestFrozenBasis
import Verification.FrozenBasisExponentCoordinates
import Verification.LaurentRowCorrection

/-!
# Path Forest Laurent Normalization

Actual frozen-coefficient normalization for the linear path forest.
AS constructs the frozen basis and mutable row correction internally. The
contragredient exponent map realizes the row basis change on the Laurent
algebra, then the mutable monomial substitution gives C_std exactly.
-/
noncomputable section
namespace Verification.PathForestLaurentNormalization
open Classical Verification.PathForestMatching Verification.PathForestFullRank
open Verification.PathForestComponentMatrix Verification.PathForestFrozenBasis
variable (R : Type) [CommRing R]
variable {S F : Type} [Fintype S] [Fintype F] (m : S → ℕ) (o : S → Bool)
variable (C : Matrix F (PIndex m o) ℤ) (G : Matrix F (QIndex m) ℤ)
variable (hAS : AnticliqueSubcolumns.AS (extended m o (fun _ _=>1) (fun _ _=>1) C G)
  (BipartiteASCoordinates.selected (PIndex m o) (QIndex m)))

def exponentCoordinates : (F → ℤ) ≃ₗ[ℤ] (NewFrozen (F:=F) o → ℤ) :=
  FrozenBasisExponentCoordinates.coordinates (basis m o C G hAS)

theorem exponent_columns (i : Vertices m o) :
    exponentCoordinates m o C G hAS (LaurentRowCorrection.column (frozenMatrix m o C G) i)=
      LaurentRowCorrection.column (changedFrozen m o C G hAS) i :=
  FrozenBasisExponentCoordinates.column_coordinates (basis m o C G hAS) (frozenMatrix m o C G) i

def basisEquiv (c : Vertices m o → Rˣ) :
    LaurentScalarModel.Presentation R (ordinaryMatrix m o) (LaurentRowCorrection.column (frozenMatrix m o C G)) c ≃ₐ[R]
      LaurentScalarModel.Presentation R (ordinaryMatrix m o) (LaurentRowCorrection.column (changedFrozen m o C G hAS)) c :=
  (LaurentScalarModel.presentationEquiv R (Equiv.refl (Vertices m o)) (exponentCoordinates m o C G hAS)
    (ordinaryMatrix m o) (LaurentRowCorrection.column (frozenMatrix m o C G)) c).trans
      (Ideal.quotientEquivAlgOfEq R (congrArg (fun f=>LaurentScalarModel.relations R (ordinaryMatrix m o) f c)
        (funext (exponent_columns m o C G hAS))))

def standardEquiv (c : Vertices m o → Rˣ) :
    LaurentScalarModel.Presentation R (ordinaryMatrix m o) (LaurentRowCorrection.column (frozenMatrix m o C G)) c ≃ₐ[R]
      LaurentScalarModel.Presentation R (ordinaryMatrix m o) (LaurentRowCorrection.column (standardFrozen (F:=F) m o)) c :=
  (basisEquiv R m o C G hAS c).trans
    (LaurentRowCorrection.presentationEquiv R (ordinaryMatrix m o) (standardFrozen (F:=F) m o)
      (changedFrozen m o C G hAS) (correction m o C G hAS) (frozen_normalform m o C G hAS) c)

#print axioms exponentCoordinates
#print axioms exponent_columns
#print axioms basisEquiv
#print axioms standardEquiv
end Verification.PathForestLaurentNormalization
