/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FinitePerturbation

/-!
# Isolated Perturbation Summand

A constant summand annihilated by both the pure and perturbed differential
is left strictly fixed by the constructed perturbation formulas. This permits
realization with an independent Z object, without giving Z the positive MW
coefficient action.
-/

namespace Verification.IsolatedPerturbationSummand

open Verification.FinitePerturbation

variable {A : Type*} [Ring A] (u h v e : A)
variable (heu : e*u=0) (hue : u*e=0) (heh : e*h=0) (hhe : h*e=0)
variable (hev : e*v=0) (hve : v*e=0)
variable (q : Aˣ) (hq : (q : A)=1+v*h)

include heu heh in
theorem projection_left : e*pureProjection u h=e := by
  simp only [pureProjection,mul_sub,mul_one,←mul_assoc,heu,heh,zero_mul,sub_zero]

include hue hhe in
theorem projection_right : pureProjection u h*e=e := by
  simp only [pureProjection,sub_mul,one_mul,mul_assoc,hue,hhe,mul_zero,sub_zero]

include hev hq in
theorem inverse_left : e*q.inv=e := by
  have heq : e*(q:A)=e := by rw [hq,mul_add,mul_one,←mul_assoc,hev,zero_mul,add_zero]
  calc e*q.inv=(e*(q:A))*q.inv := by rw [heq]
       _=e := by rw [mul_assoc,q.val_inv,mul_one]

include hhe hq in
theorem inverse_right : q.inv*e=e := by
  have hqe : (q:A)*e=e := by rw [hq,add_mul,one_mul,mul_assoc,hhe,mul_zero,add_zero]
  calc q.inv*e=q.inv*((q:A)*e) := by rw [hqe]
       _=e := by rw [←mul_assoc,q.inv_val,one_mul]

include hev hq in
theorem correction_left : e*correction v q=0 := by
  rw [correction,←mul_assoc,inverse_left h v e hev q hq,hev]

include hve in
theorem correction_right : correction v q*e=0 := by
  rw [correction,mul_assoc,hve,mul_zero]

include heh hhe in
theorem homotopy_isolated :
    e*correctedHomotopy h v q=0 ∧ correctedHomotopy h v q*e=0 := by
  constructor
  · simp only [correctedHomotopy,mul_sub,←mul_assoc,heh,zero_mul,sub_zero]
  · simp only [correctedHomotopy,sub_mul,mul_assoc,hhe,mul_zero,sub_zero]

include heu hue heh hhe hve in
theorem inclusion_isolated :
    e*correctedInclusion u h v q=e ∧ correctedInclusion u h v q*e=e := by
  have hl := projection_left u h e heu heh
  have hr := projection_right u h e hue hhe
  constructor
  · rw [correctedInclusion,mul_sub,hl]
    simp only [←mul_assoc,heh,zero_mul,sub_zero]
  · rw [correctedInclusion,sub_mul,hr,mul_assoc,hr,mul_assoc,correction_right v e hve q,mul_zero,sub_zero]

include heu hue heh hhe hev hq in
theorem retraction_isolated :
    e*correctedRetraction u h v q=e ∧ correctedRetraction u h v q*e=e := by
  have hl := projection_left u h e heu heh
  have hr := projection_right u h e hue hhe
  constructor
  · rw [correctedRetraction,mul_sub,hl,←mul_assoc,←mul_assoc,hl,
      correction_left h v e hev q hq,zero_mul,sub_zero]
  · rw [correctedRetraction,sub_mul,hr,mul_assoc,hhe,mul_zero,sub_zero]

#print axioms projection_left
#print axioms projection_right
#print axioms inverse_left
#print axioms inverse_right
#print axioms correction_left
#print axioms correction_right
#print axioms homotopy_isolated
#print axioms inclusion_isolated
#print axioms retraction_isolated

end Verification.IsolatedPerturbationSummand
