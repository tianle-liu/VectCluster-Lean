/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathPureContractionData

/-!
# Path Zero Pure Bases

Genuine length-zero path base cases: all original configurations are
empty, so the homogeneous differential itself is zero.
-/

namespace Verification.PathZeroPureBases

open Classical Verification.PathPureContractionData Verification.GradedPerturbation
  Verification.FinitePerturbation Verification.PathNormalizedBasis Verification.PathStratumGrading
  Verification.PathEndpointCoordinates Verification.PathFullComplex

variable {R : Type} [CommRing R]

noncomputable def concentratedZero {ι : Type} [Fintype ι] [DecidableEq ι]
    (d : ι → ℤ) (D : Matrix ι ι R) (hd : Homogeneous d 1 D) (h0 : ∀ i,d i=0) : Data d D := by
  have hD : D=0 := by ext i j; exact hd i j (by rw [h0 i,h0 j]; omega)
  exact {
    differential_degree := hd
    differential_square := by rw [hD,mul_zero]
    homotopy := 0
    homotopy_degree := homogeneous_zero d (-1)
    homotopy_square := mul_zero _
    homotopy_regular := by rw [zero_mul,mul_zero]
    generalized := by simp [hD]
    supported := fun i _ hi => (hi (h0 i)).elim }

theorem zero_degree (B : List Bool → Prop) (x : NormalIndex B 0) : degree x=0 := by
  have hx : x.1.val=∅ := Finset.eq_empty_iff_forall_not_mem.mpr (by
    intro i hi
    have hh := Finset.mem_Icc.mp (x.1.property.1 hi)
    omega)
  change (x.1.val.card:ℤ)=0
  rw [hx,Finset.card_empty,Int.natCast_zero]

noncomputable def zZero (g : R) : Data (fun x => -degree x) (zMatrix g 0 0).transpose :=
  concentratedZero _ _ (transpose_degree _ _ (zMatrix_degree g 0 0))
    (fun x => by rw [zero_degree,neg_zero])

noncomputable def yZero (g : R) : Data (fun x => -degree x) (yMatrix g 0 0).transpose :=
  concentratedZero _ _ (transpose_degree _ _ (yMatrix_degree g 0 0))
    (fun x => by rw [zero_degree,neg_zero])

#print axioms concentratedZero
#print axioms zero_degree
#print axioms zZero
#print axioms yZero

end Verification.PathZeroPureBases
