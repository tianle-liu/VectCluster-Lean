/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCoefficientGrading
import Verification.PathGradedMatrices
import Verification.WeightedFixedBasis

/-!
# Pure Rectangular Coefficients

A genuine weighted survivor basis yields homogeneous rectangular inverse
matrices over the formal coefficient ring. Applying rho=0 to inverse entries
removes arbitrary positive-degree coefficients without changing either inverse
identity; no freeness or basis assertion is inserted here.
-/

namespace Verification.PureRectangularCoefficients

open Verification.PathCoefficientRing Verification.PathCoefficientGrading
  Verification.SurvivorBaseChange

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem pure_idempotent : pure.comp pure=pure := by
  apply hom_ext
  · simp only [RingHom.comp_apply,pure_g]
  · simp only [RingHom.comp_apply,pure_rho,map_zero]

theorem pure_twice (r : Coeff) : pure (pure r)=pure r :=
  congrArg (fun f : Coeff →+* Coeff=>f r) pure_idempotent

noncomputable def inverse (P : Matrix ι ι Coeff) (hP : P*P=P)
    (b : Basis κ Coeff (fixedModule P)) : Matrix κ ι Coeff :=
  (retractionMatrix P hP b).map pure

theorem inclusion_inverse (P : Matrix ι ι Coeff) (hP : P*P=P)
    (b : Basis κ Coeff (fixedModule P))
    (hI : (inclusionMatrix P b).map pure=inclusionMatrix P b) (hmap : P.map pure=P) :
    inclusionMatrix P b * inverse P hP b=P := by
  have hh := congrArg (fun M : Matrix ι ι Coeff=>M.map pure) (inclusion_retraction P hP b)
  simpa only [Matrix.map_mul,hI,hmap] using hh

theorem inverse_inclusion (P : Matrix ι ι Coeff) (hP : P*P=P)
    (b : Basis κ Coeff (fixedModule P))
    (hI : (inclusionMatrix P b).map pure=inclusionMatrix P b) :
    inverse P hP b * inclusionMatrix P b=1 := by
  have hh := congrArg (fun M : Matrix κ κ Coeff=>M.map pure) (retraction_inclusion P hP b)
  simpa only [Matrix.map_mul,hI,Matrix.map_one pure (map_zero pure) (map_one pure)] using hh

omit [DecidableEq κ] in
theorem inverse_degree (w : ι → ℕ) (v : κ → ℕ) (P : Matrix ι ι Coeff) (hP : P*P=P)
    (b : Basis κ Coeff (fixedModule P)) (hwP : ∀i j,w i≠w j → P i j=0)
    (hb : ∀k i,w i≠v k → (b k).val i=0) :
    PathGradedMatrices.Homogeneous (fun k=>(v k:ℤ)) (fun i=>(w i:ℤ)) (inverse P hP b) := by
  intro k i
  by_cases he : v k=w i
  · change PathCoefficientGrading.Homogeneous ((v k:ℤ)-w i) (pure (retractionMatrix P hP b k i))
    rw [he,sub_self]
    exact pure_homogeneous _
  · change PathCoefficientGrading.Homogeneous _ (pure (retractionMatrix P hP b k i))
    rw [WeightedFixedBasis.retraction_support w v P hP b hwP hb k i he,map_zero]
    exact homogeneous_zero _

#print axioms pure_idempotent
#print axioms pure_twice
#print axioms inverse
#print axioms inclusion_inverse
#print axioms inverse_inclusion
#print axioms inverse_degree

end Verification.PureRectangularCoefficients
