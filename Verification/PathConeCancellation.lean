/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathConeCorrection

/-!
# Path Cone Cancellation

Actual simultaneous cancellation of the diagonal path-cone summands.
Only the two inductively supplied normalized contractions and the original
connecting-chain identity are inputs; all corrected cone maps are constructed.
-/

namespace Verification.PathConeCancellation

open Verification.PathConeBlocks Verification.PathConeCorrection Verification.FinitePerturbation

variable {R : Type*} [CommRing R]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

variable (A H : Matrix ι ι R) (B K : Matrix κ κ R) (C : Matrix ι κ R)
variable (hA : A*A=0) (hB : B*B=0) (hC : A*C+C*B=0)
variable (hH : H*H=0) (hK : K*K=0) (hHAH : H*A*H=H) (hKBK : K*B*K=K)
variable (hAHA : A*H*A=A) (hBKB : B*K*B=B)

def cancellation :
    MatrixRetraction (diagonal A B+upper C) (pureProjection (diagonal A B) (diagonal H K)) := by
  let U := diagonal A B
  let L := diagonal H K
  let V := upper C
  let q := coneUnit H K C
  let l := otherConeUnit H K C
  have hU : U*U=0 := by
    change diagonal A B*diagonal A B=0
    rw [diagonal_mul,hA,hB,diagonal_zero]
  have hL : L*L=0 := by
    change diagonal H K*diagonal H K=0
    rw [diagonal_mul,hH,hK,diagonal_zero]
  have hLUL : L*U*L=L := by
    change diagonal H K*diagonal A B*diagonal H K=diagonal H K
    rw [diagonal_mul,diagonal_mul,hHAH,hKBK]
  have hULU : U*L*U=U := by
    change diagonal A B*diagonal H K*diagonal A B=diagonal A B
    rw [diagonal_mul,diagonal_mul,hAHA,hBKB]
  have hD : (U+V)*(U+V)=0 := cone_square A B C hA hB hC
  have hq : (q : Matrix (ι ⊕ κ) (ι ⊕ κ) R)=1+V*L := rfl
  have hl : (l : Matrix (ι ⊕ κ) (ι ⊕ κ) R)=1+L*V := rfl
  exact {
    differential := residualDifferential U L V q
    inclusion := correctedInclusion U L V q
    retraction := correctedRetraction U L V q
    homotopy := correctedHomotopy L V q
    square := residual_square U L V hU hL hLUL hULU q l hq hl hD
    inclusion_chain := corrected_inclusion_chain U L V hU hL hLUL hULU q l hq hl hD
    retraction_chain := corrected_retraction_chain U L V hU hL hLUL hULU q l hq hl hD
    retract := corrected_retraction_inclusion U L V hU hL hLUL hULU q
    homotopy_identity := corrected_homotopy_identity U L V hU hL hLUL hULU q l hq hl hD
    homotopy_square := corrected_homotopy_square L V hL q
    homotopy_regular := corrected_homotopy_regular U L V hU hL hLUL hULU q l hq hl hD }

theorem transferred_boundary :
    (cancellation A H B K C hA hB hC hH hK hHAH hKBK hAHA hBKB).differential=
      upper (pureProjection A H*C*pureProjection B K) := residual_eq A H B K C

theorem constructed_homotopy :
    (cancellation A H B K C hA hB hC hH hK hHAH hKBK hAHA hBKB).homotopy=
      diagonal H K-upper (H*C*K) := homotopy_eq H K C

theorem constructed_inclusion :
    (cancellation A H B K C hA hB hC hH hK hHAH hKBK hAHA hBKB).inclusion=
      diagonal (pureProjection A H) (pureProjection B K)-upper (H*C*pureProjection B K) :=
  inclusion_eq A H B K C

theorem constructed_retraction :
    (cancellation A H B K C hA hB hC hH hK hHAH hKBK hAHA hBKB).retraction=
      diagonal (pureProjection A H) (pureProjection B K)-upper (pureProjection A H*C*K) :=
  retraction_eq A H B K C

#print axioms cancellation
#print axioms transferred_boundary
#print axioms constructed_homotopy
#print axioms constructed_inclusion
#print axioms constructed_retraction

end Verification.PathConeCancellation
