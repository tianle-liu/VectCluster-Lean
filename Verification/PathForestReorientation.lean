/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestRootedCertificate
import Verification.FZForestMutationInput
import Verification.ForestMutationTransport
import Verification.EmptyColumnRetraction
import Verification.FrozenGlobalAlgebraComparison

/-!
# Path Forest Reorientation

The arbitrary signed path forest is transported to an actual linearly
oriented extended matrix. Full splitting and every terminal AS family are
proved internally; the only inputs are the uniform FZ/BFZ forest theorems.
-/
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Verification.PathForestReorientation
open Classical Verification.PathForestOrientation Verification.PathForestFullRank
open Verification.RootedForestCertificate Verification.RectangularSourceSinkMutation
open Verification.RectangularMutationSequence
variable {S F : Type} [Fintype S] [Fintype F]
variable (m : S→ℕ) (o : S→Bool) (a : S→ℕ→ℤˣ) (n : ℕ)
variable (e : Vertex m o≃Fin n) (B : Matrix (Fin n⊕F) (Fin n⊕Empty) ℤ)
variable (hprincipal : ∀i j,EmptyColumnRetraction.cut B (Sum.inl (e i)) (e j)=matrix m o a i j)
variable (hAS : ∀I,ExchangeReindex.PrincipalIndependent (EmptyColumnRetraction.cut B) I→
  AnticliqueSubcolumns.AS (EmptyColumnRetraction.cut B) I)

def shape : Forest (Fin n) := (PathForestRootedCertificate.shape m o).transport e

def target : Matrix (Fin n) (Fin n) ℤ :=
  fun i j=>PathForestComponentPresentation.blockMatrix m o (e.symm i) (e.symm j)

def linearLabel : PathForestComponentMatrix.Vertices m o≃Fin n := (reindex m o).trans e

include hprincipal in
omit [Fintype S] [Fintype F] in
theorem skew : Skew (EmptyColumnRetraction.cut B) := by
  intro i j
  obtain ⟨i,rfl⟩:=e.surjective i
  obtain ⟨j,rfl⟩:=e.surjective j
  rw [hprincipal,hprincipal]
  exact PathForestRootedCertificate.skew m o a i j

omit [Fintype S] [Fintype F] in
theorem target_skew (i j : Fin n) : target m o n e i j= -target m o n e j i := by
  exact PathForestRootedCertificate.skew m o (fun _ _=>1) (e.symm i) (e.symm j)

include hprincipal in
omit [Fintype S] [Fintype F] in
theorem support (i j : Fin n) :
    EmptyColumnRetraction.cut B (Sum.inl i) j≠0 ↔ (shape m o n e).Adj i j := by
  change _ ↔ ((PathForestRootedCertificate.shape m o).transport e).Adj i j
  rw [Forest.transport_adj]
  have hp:=hprincipal (e.symm i) (e.symm j)
  simp only [Equiv.apply_symm_apply] at hp
  rw [hp]
  exact PathForestRootedCertificate.support m o a _ _

include hprincipal in
omit [Fintype S] [Fintype F] in
theorem absolute (i j : Fin n) : |target m o n e i j|=|EmptyColumnRetraction.cut B (Sum.inl i) j| := by
  have hp:=hprincipal (e.symm i) (e.symm j)
  simp only [Equiv.apply_symm_apply] at hp
  rw [hp]
  exact (PathForestRootedCertificate.absolute m o a _ _).symm

include hprincipal in
omit [Fintype F] in
theorem parity_principal (i j : PathForestComponentMatrix.Vertices m o) :
    EmptyColumnRetraction.cut B (Sum.inl (linearLabel m o n e i)) (linearLabel m o n e j)=
      principal m o (leftSigns m o a) (rightSigns m o a) i j := by
  change EmptyColumnRetraction.cut B (Sum.inl (e (reindex m o i))) (e (reindex m o j))=_
  rw [hprincipal]
  exact congrFun (congrFun (matrix_reindex m o a) i) j

def initialRetraction : ((Fin n⊕F)→ℤ)→ₗ[ℤ](Fin n→ℤ) :=
  PathForestOriginalRFR.retraction m o (leftSigns m o a) (rightSigns m o a)
    (linearLabel m o n e) (EmptyColumnRetraction.cut B)
    (parity_principal m o a n e B hprincipal) hAS

theorem initial_left : (initialRetraction m o a n e B hprincipal hAS).comp
    (EmptyColumnRetraction.cut B).mulVecLin=LinearMap.id :=
  PathForestOriginalRFR.left m o (leftSigns m o a) (rightSigns m o a)
    (linearLabel m o n e) (EmptyColumnRetraction.cut B)
    (parity_principal m o a n e B hprincipal) hAS

variable (Q : FZForestMutationInput.Standard)
def sequence : List (Fin n) := Classical.choose
  (Q.reorient (Fin n) F (shape m o n e) (EmptyColumnRetraction.cut B) (target m o n e)
    (skew m o a n e B hprincipal) (target_skew m o n e)
    (support m o a n e B hprincipal) (absolute m o a n e B hprincipal))

omit [Fintype S] in
theorem sequence_admissible : Admissible (EmptyColumnRetraction.cut B) (sequence m o a n e B hprincipal Q) :=
  (Classical.choose_spec (Q.reorient (Fin n) F (shape m o n e) (EmptyColumnRetraction.cut B) (target m o n e)
    (skew m o a n e B hprincipal) (target_skew m o n e)
    (support m o a n e B hprincipal) (absolute m o a n e B hprincipal))).1

omit [Fintype S] in
theorem sequence_target : ∀i j,result (EmptyColumnRetraction.cut B) (sequence m o a n e B hprincipal Q)
    (Sum.inl i) j=target m o n e i j :=
  (Classical.choose_spec (Q.reorient (Fin n) F (shape m o n e) (EmptyColumnRetraction.cut B) (target m o n e)
    (skew m o a n e B hprincipal) (target_skew m o n e)
    (support m o a n e B hprincipal) (absolute m o a n e B hprincipal))).2

def linearMatrix : Matrix (Fin n⊕F) (Fin n⊕Empty) ℤ :=
  BFZForestMutationInput.extended (result (EmptyColumnRetraction.cut B) (sequence m o a n e B hprincipal Q))

theorem linear_principal (i j : PathForestComponentMatrix.Vertices m o) :
    linearMatrix m o a n e B hprincipal Q (Sum.inl (linearLabel m o n e i)) (Sum.inl (linearLabel m o n e j))=
      PathForestComponentMatrix.ordinaryMatrix m o i j := by
  change result _ _ _ _=_
  rw [sequence_target]
  change PathForestComponentPresentation.blockMatrix m o (e.symm (e (reindex m o i)))
    (e.symm (e (reindex m o j)))=_
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  exact congrFun (congrFun (PathForestComponentPresentation.linear_reindex m o) i) j

include hAS in
theorem linear_AS (I : Finset (Fin n))
    (hI : ExchangeReindex.PrincipalIndependent (EmptyColumnRetraction.cut (linearMatrix m o a n e B hprincipal Q)) I) :
    AnticliqueSubcolumns.AS (EmptyColumnRetraction.cut (linearMatrix m o a n e B hprincipal Q)) I :=
  RectangularMutationSequence.selected_AS (EmptyColumnRetraction.cut B) (skew m o a n e B hprincipal)
    (initialRetraction m o a n e B hprincipal hAS) (initial_left m o a n e B hprincipal hAS)
    (sequence m o a n e B hprincipal Q) (sequence_admissible m o a n e B hprincipal Q) I hI

variable (R : Type) [Field R] (H : BFZForestMutationInput.Standard R)
def algebraEquiv : FrozenAcyclicCover.Global R F n B ≃ₐ[R]
    FrozenAcyclicCover.Global R F n (linearMatrix m o a n e B hprincipal Q) := by
  have hb : BFZForestMutationInput.extended (EmptyColumnRetraction.cut B)=B := by
    funext r i
    cases i with
    | inl i=>rfl
    | inr i=>exact i.elim
  have e' := ForestMutationTransport.equiv R H (shape m o n e) (EmptyColumnRetraction.cut B)
    (skew m o a n e B hprincipal) (support m o a n e B hprincipal)
    (sequence m o a n e B hprincipal Q) (sequence_admissible m o a n e B hprincipal Q)
  rw [hb] at e'
  exact (FrozenGlobalAlgebraComparison.equiv R F n B).trans
    (e'.trans (FrozenGlobalAlgebraComparison.equiv R F n
      (linearMatrix m o a n e B hprincipal Q)).symm)

#print axioms shape
#print axioms target
#print axioms linearLabel
#print axioms skew
#print axioms target_skew
#print axioms support
#print axioms absolute
#print axioms parity_principal
#print axioms initialRetraction
#print axioms initial_left
#print axioms sequence
#print axioms sequence_admissible
#print axioms sequence_target
#print axioms linearMatrix
#print axioms linear_principal
#print axioms linear_AS
#print axioms algebraEquiv
end Verification.PathForestReorientation
