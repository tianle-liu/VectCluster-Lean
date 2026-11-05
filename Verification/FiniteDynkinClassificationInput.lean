/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.DynkinMatrixNormalForm
import Mathlib.Data.Real.Basic

/-!
# Finite Dynkin Classification Input

Ordinary finite Cartan classification, as used in Fomin--Zelevinsky II,
Section 1.3 and the Dynkin list in Section 9 (arXiv:math/0208229).
The hypothesis is the actual positive-definite symmetrized Cartan companion;
the conclusion is an explicit relabeling of the original integer matrix.
No deletion, path-forest, strict complex, or cohomological conclusion is an input.
-/
noncomputable section
namespace Verification.FiniteDynkinClassificationInput
open Classical
open scoped BigOperators
variable {n : ℕ}

def companion (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : ℝ :=
  if i=j then 2 else -((|B i j|:ℤ):ℝ)

def FiniteCartan (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃d : Fin n→ℝ,(∀i,0<d i) ∧ (∀i j,d i*(B i j:ℝ)= -d j*(B j i:ℝ)) ∧
    ∀x : Fin n→ℝ,x≠0→0<∑i,∑j,x i*d i*companion B i j*x j

def Indecomposable (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  Nonempty (Fin n) ∧ ∀I : Finset (Fin n),I.Nonempty→I≠Finset.univ→
    ∃i∈I,∃j∉I,B i j≠0 ∨ B j i≠0

structure Standard where
  classify : ∀n (B : Matrix (Fin n) (Fin n) ℤ),FiniteCartan B→Indecomposable B→
    Nonempty (DynkinMatrixNormalForm.NormalForm n B)

#print axioms companion
#print axioms FiniteCartan
#print axioms Indecomposable
#print axioms Standard
end Verification.FiniteDynkinClassificationInput
