/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathConeBlocks

/-!
# Path Cone Correction

Explicit finite cone correction: its inverse has exactly two terms, and
the transferred boundary is the original connecting map between survivors.
-/

namespace Verification.PathConeCorrection

open Verification.PathConeBlocks Verification.FinitePerturbation

section Ring
variable {A : Type*} [Ring A]

def squareZeroUnit (N : A) (hN : N*N=0) : Aˣ where
  val := 1+N
  inv := 1-N
  val_inv := by noncomm_ring [hN]
  inv_val := by noncomm_ring [hN]
end Ring

variable {R : Type*} [CommRing R]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def coneUnit (H : Matrix ι ι R) (K : Matrix κ κ R) (C : Matrix ι κ R) :
    (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
  squareZeroUnit (upper C*diagonal H K) (upper_homotopy_square H K C)

def otherConeUnit (H : Matrix ι ι R) (K : Matrix κ κ R) (C : Matrix ι κ R) :
    (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
  squareZeroUnit (diagonal H K*upper C) (homotopy_upper_square H K C)

theorem correction_eq (H : Matrix ι ι R) (K : Matrix κ κ R) (C : Matrix ι κ R) :
    correction (upper C) (coneUnit H K C)=upper C := by
  change (1-upper C*diagonal H K)*upper C=upper C
  rw [sub_mul,one_mul,upper_homotopy_upper,sub_zero]

theorem residual_eq (A H : Matrix ι ι R) (B K : Matrix κ κ R) (C : Matrix ι κ R) :
    residualDifferential (diagonal A B) (diagonal H K) (upper C) (coneUnit H K C)=
      upper (pureProjection A H*C*pureProjection B K) := by
  rw [residualDifferential,correction_eq,diagonal_projection,diagonal_upper,upper_diagonal]

theorem homotopy_eq (H : Matrix ι ι R) (K : Matrix κ κ R) (C : Matrix ι κ R) :
    correctedHomotopy (diagonal H K) (upper C) (coneUnit H K C)=
      diagonal H K-upper (H*C*K) := by
  rw [correctedHomotopy,correction_eq,diagonal_upper,upper_diagonal]

theorem inclusion_eq (A H : Matrix ι ι R) (B K : Matrix κ κ R) (C : Matrix ι κ R) :
    correctedInclusion (diagonal A B) (diagonal H K) (upper C) (coneUnit H K C)=
      diagonal (pureProjection A H) (pureProjection B K)-upper (H*C*pureProjection B K) := by
  rw [correctedInclusion,correction_eq,diagonal_projection,diagonal_upper,upper_diagonal]

theorem retraction_eq (A H : Matrix ι ι R) (B K : Matrix κ κ R) (C : Matrix ι κ R) :
    correctedRetraction (diagonal A B) (diagonal H K) (upper C) (coneUnit H K C)=
      diagonal (pureProjection A H) (pureProjection B K)-upper (pureProjection A H*C*K) := by
  rw [correctedRetraction,correction_eq,diagonal_projection,diagonal_upper,upper_diagonal]

#print axioms squareZeroUnit
#print axioms coneUnit
#print axioms otherConeUnit
#print axioms correction_eq
#print axioms residual_eq
#print axioms homotopy_eq
#print axioms inclusion_eq
#print axioms retraction_eq

end Verification.PathConeCorrection
