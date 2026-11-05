/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SubsetProjectionComplex

/-!
# Selected Witt Incidence Sign

The normal-order exponent on the actual selected-coordinate subtype
is the original finite-set incidence exponent in the integer complex.
-/
noncomputable section
open scoped Classical
namespace Verification.SelectedWittIncidenceSign
variable {V : Type*} [LinearOrder V] (J : Finset V) (v : J)

theorem count : ((Finset.univ.erase v).filter (fun i : J => i<v)).card =
    (J.filter (fun i => i<v.val)).card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨i.property,(Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact Subtype.ext hij
  · intro j hj
    obtain ⟨hjJ,hjv⟩ := Finset.mem_filter.mp hj
    refine ⟨⟨j,hjJ⟩,?_,rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_erase.mpr ⟨fun h => (ne_of_lt hjv) (congrArg Subtype.val h),Finset.mem_univ _⟩,hjv⟩

theorem sign : ((-1 : ℤ)^((Finset.univ.erase v).filter (fun i : J => i<v)).card) =
    Verification.SubsetProjectionComplex.sign J v.val := by
  rw [count]
  rfl

#print axioms count
#print axioms sign
end Verification.SelectedWittIncidenceSign
