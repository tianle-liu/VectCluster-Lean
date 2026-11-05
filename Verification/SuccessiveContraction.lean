/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FinitePerturbation

/-!
# Successive Contraction

Successive cancellation: a generalized inverse of the actually transferred
differential lifts through the previously constructed retraction.
-/

namespace Verification.SuccessiveContraction

open Verification.FinitePerturbation

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem differential_decomposition (D P : Matrix ι ι R) (hD : D*D=0)
    (T : MatrixRetraction D P) :
    D*T.homotopy*D+T.inclusion*T.differential*T.retraction=D := by
  have hh := congrArg (fun A : Matrix ι ι R => A*D) T.homotopy_identity
  simp only [sub_mul,one_mul,mul_assoc,T.retraction_chain,hD,mul_zero,sub_zero] at hh
  calc
    D*T.homotopy*D+T.inclusion*T.differential*T.retraction=
        D*(T.homotopy*D)+(D-D*(T.homotopy*D)) := by rw [mul_assoc,mul_assoc,hh]
    _=D := by abel

theorem generalized (D P : Matrix ι ι R) (hD : D*D=0) (T : MatrixRetraction D P)
    (K : Matrix ι ι R) (hK : T.differential*K*T.differential=T.differential) :
    D*(T.homotopy+T.inclusion*K*T.retraction)*D=D := by
  calc
    D*(T.homotopy+T.inclusion*K*T.retraction)*D=
        D*T.homotopy*D+T.inclusion*(T.differential*K*T.differential)*T.retraction := by
      rw [mul_add,add_mul]
      congr 1
      calc
        D*(T.inclusion*K*T.retraction)*D=
            (D*T.inclusion)*K*(T.retraction*D) := by simp only [mul_assoc]
        _=(T.inclusion*T.differential)*K*(T.differential*T.retraction) := by
          rw [T.inclusion_chain,T.retraction_chain]
        _=T.inclusion*(T.differential*K*T.differential)*T.retraction := by simp only [mul_assoc]
    _=D := by rw [hK]; exact differential_decomposition D P hD T

#print axioms differential_decomposition
#print axioms generalized

end Verification.SuccessiveContraction
