/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PositiveMatrixRestriction
import Verification.GradedRectangularHomotopy
import Verification.GradedPerturbation

/-!
# Positive Graded Contraction

Realization of an already proved homogeneous rectangular contraction on
its positive-weight indices. The path applications construct every field from
the actual full matrices; the constant object is added separately.
-/

noncomputable section
namespace Verification.PositiveGradedContraction

open Classical CategoryTheory Verification.PathCoefficientRing
  Verification.GradedCoefficientCategory Verification.GradedMatrixComplex
  Verification.PositiveMatrixRestriction

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

structure Data (w : ι → ℕ) (v : κ → ℕ) (d : ι → ℤ) where
  D : Matrix ι ι Coeff
  H : Matrix ι ι Coeff
  I : Matrix ι κ Coeff
  J : Matrix κ ι Coeff
  coefficientD : PathGradedMatrices.Homogeneous (fun i=>(w i:ℤ)) (fun i=>(w i:ℤ)) D
  coefficientH : PathGradedMatrices.Homogeneous (fun i=>(w i:ℤ)) (fun i=>(w i:ℤ)) H
  coefficientI : PathGradedMatrices.Homogeneous (fun i=>(w i:ℤ)) (fun k=>(v k:ℤ)) I
  coefficientJ : PathGradedMatrices.Homogeneous (fun k=>(v k:ℤ)) (fun i=>(w i:ℤ)) J
  degreeD : GradedPerturbation.Homogeneous d 1 D
  degreeH : GradedPerturbation.Homogeneous d (-1) H
  degreeI : ∀i k,d i≠0 → I i k=0
  degreeJ : ∀k i,d i≠0 → J k i=0
  square : D*D=0
  chainI : D*I=0
  chainJ : J*D=0
  retract : J*I=1
  homotopy : I*J=1-D*H-H*D
  crossD : ∀i j,0<w i → w j=0 → D i j=0
  crossH : ∀i j,0<w i → w j=0 → H i j=0
  crossI : ∀i k,0<w i → v k=0 → I i k=0
  crossJ : ∀k i,0<v k → w i=0 → J k i=0

def positiveSpace (w : ι → ℕ) : Space where
  index := {i // 0<w i}
  finite := inferInstance
  decidable := inferInstance
  weight := fun i=>w i.val-1

variable {w : ι → ℕ} {v : κ → ℕ} {d : ι → ℤ} (T : Data w v d)

def differential : positiveSpace w ⟶ positiveSpace w := ⟨restrict w w T.D,degree w w T.D T.coefficientD⟩
def contraction : positiveSpace w ⟶ positiveSpace w := ⟨restrict w w T.H,degree w w T.H T.coefficientH⟩
def inclusion : positiveSpace v ⟶ positiveSpace w := ⟨restrict w v T.I,degree w v T.I T.coefficientI⟩
def retraction : positiveSpace w ⟶ positiveSpace v := ⟨restrict v w T.J,degree v w T.J T.coefficientJ⟩

theorem differential_supported : Supported (fun i : {i // 0<w i}=>d i.val) (fun i : {i // 0<w i}=>d i.val) 1 (differential T) :=
  fun i j hij=>T.degreeD i.val j.val hij

theorem contraction_supported : Supported (fun i : {i // 0<w i}=>d i.val) (fun i : {i // 0<w i}=>d i.val) (-1) (contraction T) :=
  fun i j hij=>T.degreeH i.val j.val hij

theorem inclusion_supported : Supported (fun _ : {k // 0<v k}=>(0:ℤ)) (fun i : {i // 0<w i}=>d i.val) 0 (inclusion T) := by
  intro i k hi
  exact T.degreeI i.val k.val (by simpa using hi)

theorem retraction_supported : Supported (fun i : {i // 0<w i}=>d i.val) (fun _ : {k // 0<v k}=>(0:ℤ)) 0 (retraction T) := by
  intro k i hi
  dsimp only at hi
  exact T.degreeJ k.val i.val (by omega)

theorem differential_square : differential T≫differential T=0 := by
  apply Subtype.ext
  change restrict w w T.D*restrict w w T.D=0
  rw [product w w w T.D T.D T.crossD,T.square]
  rfl

theorem inclusion_chain : inclusion T≫differential T=0 := by
  apply Subtype.ext
  change restrict w w T.D*restrict w v T.I=0
  rw [product w w v T.D T.I T.crossD,T.chainI]
  rfl

theorem retraction_chain : differential T≫retraction T=0 := by
  apply Subtype.ext
  change restrict v w T.J*restrict w w T.D=0
  rw [product v w w T.J T.D T.crossJ,T.chainJ]
  rfl

theorem inclusion_retraction : inclusion T≫retraction T=𝟙 (positiveSpace v) := by
  apply Subtype.ext
  change restrict v w T.J*restrict w v T.I=1
  rw [product v w v T.J T.I T.crossJ,T.retract,identity]

theorem homotopy_identity : retraction T≫inclusion T=
    𝟙 (positiveSpace w)-(differential T≫contraction T)-(contraction T≫differential T) := by
  apply Subtype.ext
  change restrict w v T.I*restrict v w T.J=
    (1 : Matrix {i // 0<w i} {i // 0<w i} Coeff)-restrict w w T.H*restrict w w T.D-restrict w w T.D*restrict w w T.H
  rw [product w v w T.I T.J T.crossI,product w w w T.H T.D T.crossH,
    product w w w T.D T.H T.crossD,T.homotopy,←identity w]
  ext i j
  change (1-T.D*T.H-T.H*T.D) i.val j.val=
    (1 : Matrix ι ι Coeff) i.val j.val-(T.H*T.D) i.val j.val-(T.D*T.H) i.val j.val
  simp only [Matrix.sub_apply]
  abel

def equivalence : HomotopyEquiv
    (complex (positiveSpace w) (fun i : {i // 0<w i}=>d i.val) (differential T)
      (differential_supported T) (differential_square T))
    (complex (positiveSpace v) (fun _=>0) 0 (supported_zero _ _ 1) (by simp)) :=
  GradedRectangularHomotopy.equivalence _ _ (differential T) (contraction T) (inclusion T) (retraction T)
    (differential_supported T) (contraction_supported T) (inclusion_supported T) (retraction_supported T)
    (differential_square T) (inclusion_chain T) (retraction_chain T)
    (inclusion_retraction T) (homotopy_identity T)

#print axioms Data
#print axioms positiveSpace
#print axioms differential
#print axioms contraction
#print axioms inclusion
#print axioms retraction
#print axioms differential_supported
#print axioms contraction_supported
#print axioms inclusion_supported
#print axioms retraction_supported
#print axioms differential_square
#print axioms inclusion_chain
#print axioms retraction_chain
#print axioms inclusion_retraction
#print axioms homotopy_identity
#print axioms equivalence

end Verification.PositiveGradedContraction
