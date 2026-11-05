/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.NormalFrameInsertion

/-!
# Selected Normal Orientation

The local Selected-stratum order has exactly the manuscript's original
vertex incidence count. No permutation or orientation factor is assumed.
-/

namespace Verification.SelectedNormalOrientation
open Finset
variable {V : Type*} [LinearOrder V] (J : Finset V) (v : J)

theorem below_card : ((univ.erase v).filter (fun i : J=>i<v)).card=
    ((J.erase v.val).filter (fun i : V=>i<v.val)).card := by
  classical
  refine card_bij (fun i _=>i.val) ?_ ?_ ?_
  · intro i hi
    obtain ⟨hi,hlt⟩:=mem_filter.mp hi
    exact mem_filter.mpr ⟨mem_erase.mpr ⟨by
      intro h
      exact (ne_of_mem_erase hi) (Subtype.ext h),i.property⟩,hlt⟩
  · intro i _ j _ h
    exact Subtype.ext h
  · intro i hi
    obtain ⟨hi,hlt⟩:=mem_filter.mp hi
    refine ⟨⟨i,mem_of_mem_erase hi⟩,mem_filter.mpr ⟨mem_erase.mpr ⟨?_,mem_univ _⟩,hlt⟩,rfl⟩
    intro h
    exact (ne_of_mem_erase hi) (congrArg Subtype.val h)

theorem orientation_factor {M : Type*} [Monoid M] (orientation : ℤˣ →* M) :
    orientation (Equiv.Perm.sign (NormalFrameInsertion.permutation (univ.erase v) v (by simp)))=
      orientation (-1)^((J.erase v.val).filter (fun i : V=>i<v.val)).card := by
  classical
  rw [NormalFrameInsertion.orientation_factor,below_card]

#print axioms below_card
#print axioms orientation_factor
end Verification.SelectedNormalOrientation
