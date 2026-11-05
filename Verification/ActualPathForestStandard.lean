/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarGlobalFunctionLaurent
import Verification.PathForestLaurentNormalization
import Verification.PathForestScalarNormalization
import Verification.OriginalScalarOne

/-!
# Actual Path Forest Standard

The actual Global algebra of a linear path forest is isomorphic to its
standard endpoint-coefficient Laurent presentation. Arbitrary scalar and frozen
coefficients are removed using AS; the coordinate algebra is the original one.
-/
noncomputable section
namespace Verification.ActualPathForestStandard
open Classical Verification.PathForestFullRank Verification.PathForestComponentMatrix
variable (R : Type) [CommRing R] {S F : Type} [Fintype S] [Fintype F]
variable (m : S → ℕ) (o : S → Bool) (n : ℕ) (e : Vertices m o ≃ Fin n)
variable (B : Matrix (Fin n ⊕ F) (Fin n ⊕ Empty) ℤ)
variable (hprincipal : ∀ i j,B (Sum.inl (e i)) (Sum.inl (e j))=ordinaryMatrix m o i j)
variable (hAS : ∀ I,ExchangeReindex.PrincipalIndependent (EmptyColumnRetraction.cut B) I →
  AnticliqueSubcolumns.AS (EmptyColumnRetraction.cut B) I)

def frozenP : Matrix F (PIndex m o) ℤ := PathForestOriginalRFR.frozenP m o e (EmptyColumnRetraction.cut B)
def frozenQ : Matrix F (QIndex m) ℤ := PathForestOriginalRFR.frozenQ m o e (EmptyColumnRetraction.cut B)

include hprincipal hAS in
theorem selected_AS : AnticliqueSubcolumns.AS
    (extended m o (fun _ _=>1) (fun _ _=>1) (frozenP m o n e B) (frozenQ m o n e B))
      (BipartiteASCoordinates.selected (PIndex m o) (QIndex m)) :=
  PathForestOriginalRFR.selected_AS m o (fun _ _=>1) (fun _ _=>1) e (EmptyColumnRetraction.cut B) hprincipal hAS

include hprincipal in
omit [Fintype F] in
theorem coordinate_relations :
    LaurentScalarModel.relations R (ScalarGlobalFunctionLaurent.principal F (Vertices m o) n e B)
      (LaurentRowCorrection.column (ScalarGlobalFunctionLaurent.frozen F (Vertices m o) n e B))
      (ScalarGlobalFunctionLaurent.scalar R (Vertices m o) n e (fun _=>1) (fun _=>1))=
    LaurentScalarModel.relations R (ordinaryMatrix m o)
      (LaurentRowCorrection.column (PathForestFrozenBasis.frozenMatrix m o (frozenP m o n e B) (frozenQ m o n e B)))
      (fun _=>1) := by
  have hp : ScalarGlobalFunctionLaurent.principal F (Vertices m o) n e B=ordinaryMatrix m o :=
    funext (fun i=>funext (fun j=>hprincipal i j))
  have hf : ScalarGlobalFunctionLaurent.frozen F (Vertices m o) n e B=
      PathForestFrozenBasis.frozenMatrix m o (frozenP m o n e B) (frozenQ m o n e B) := by
    ext k i
    cases i <;> rfl
  have hc : ScalarGlobalFunctionLaurent.scalar R (Vertices m o) n e (fun _=>1) (fun _=>1)=(fun _=>1) := by
    funext i
    simp [ScalarGlobalFunctionLaurent.scalar]
  rw [hp,hf,hc]

def coordinateEquiv : ScalarFrozenGlobal.Global R F n B (fun _=>1) (fun _=>1) ≃ₐ[R]
    LaurentScalarModel.Presentation R (ordinaryMatrix m o)
      (LaurentRowCorrection.column (PathForestFrozenBasis.frozenMatrix m o (frozenP m o n e B) (frozenQ m o n e B)))
      (fun _=>1) :=
  (ScalarGlobalFunctionLaurent.globalEquiv R F (Vertices m o) n e B (fun _=>1) (fun _=>1)).trans
    (Ideal.quotientEquivAlgOfEq R (coordinate_relations R m o n e B hprincipal))

def standardEquiv (a b : Fin n → Rˣ) : ScalarFrozenGlobal.Global R F n B a b ≃ₐ[R]
    LaurentScalarModel.Presentation R (ordinaryMatrix m o)
      (LaurentRowCorrection.column (PathForestFrozenBasis.standardFrozen (F:=F) m o)) (fun _=>1) :=
  (PathForestScalarNormalization.globalEquiv R m o (fun _ _=>1) (fun _ _=>1) n e B hprincipal hAS a b).trans
    ((coordinateEquiv R m o n e B hprincipal).trans
      (PathForestLaurentNormalization.standardEquiv R m o (frozenP m o n e B) (frozenQ m o n e B)
        (selected_AS m o n e B hprincipal hAS) (fun _=>1)))

def originalEquiv : FrozenAcyclicCover.Global R F n B ≃ₐ[R]
    LaurentScalarModel.Presentation R (ordinaryMatrix m o)
      (LaurentRowCorrection.column (PathForestFrozenBasis.standardFrozen (F:=F) m o)) (fun _=>1) :=
  (OriginalScalarOne.globalEquiv R F n B).trans
    ((coordinateEquiv R m o n e B hprincipal).trans
      (PathForestLaurentNormalization.standardEquiv R m o (frozenP m o n e B) (frozenQ m o n e B)
        (selected_AS m o n e B hprincipal hAS) (fun _=>1)))

#print axioms frozenP
#print axioms frozenQ
#print axioms selected_AS
#print axioms coordinate_relations
#print axioms coordinateEquiv
#print axioms standardEquiv
#print axioms originalEquiv
end Verification.ActualPathForestStandard
