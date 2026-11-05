/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExteriorTotalBasis

/-!
# Orientation Words

Changing a finite vertex order changes each actual exterior simplex word by
the sign of its explicitly constructed enumeration permutation.
-/

namespace Verification.OrientationWords

open Verification.EvenGraphBridge

variable {R V : Type*} [CommRing R] [DecidableEq V]

/-- The literal enumeration of a subset in a specified vertex order. -/
noncomputable def enumeration (o : LinearOrder V) (A : Finset V) : Fin A.card ≃ {v // v ∈ A} :=
  (@Finset.orderIsoOfFin V o A A.card rfl).toEquiv

/-- The permutation carrying the first enumeration to the second one. -/
noncomputable def permutation (o₁ o₂ : LinearOrder V) (A : Finset V) : Equiv.Perm (Fin A.card) :=
  (enumeration o₂ A).trans (enumeration o₁ A).symm

/-- Exterior orientation with a fixed coordinate basis, independent of ordering instances. -/
noncomputable def orderedWord (o : LinearOrder V) (A : Finset V) : ExteriorAlgebra R (V → R) :=
  ExteriorAlgebra.ιMulti R A.card (fun k => Pi.single (enumeration o A k).val 1)

/-- The actual integer unit measuring the order change. -/
noncomputable def orientation (o₁ o₂ : LinearOrder V) (A : Finset V) : ℤˣ :=
  Equiv.Perm.sign (permutation o₁ o₂ A)

/-- The exterior word changes by precisely the sign of that enumeration permutation. -/
theorem orderedWord_change (o₁ o₂ : LinearOrder V) (A : Finset V) :
    orderedWord (R := R) o₂ A=orientation o₁ o₂ A • orderedWord (R := R) o₁ A := by
  have he : (fun k => Pi.single (enumeration o₂ A k).val (1:R))=
      (fun k => Pi.single (enumeration o₁ A k).val (1:R)) ∘ permutation o₁ o₂ A := by
    funext k
    simp [permutation]
  unfold orderedWord
  rw [he]
  exact (ExteriorAlgebra.ιMulti R A.card).map_perm _ _

/-- Agreement with the independently defined sorted word used by the graph boundary. -/
theorem orderedWord_sorted (o : LinearOrder V) (A : Finset V) :
    orderedWord (R := R) o A=(letI := o; word (R := R) (A.sort (· ≤ ·))) := by
  letI := o
  rw [← Verification.ExteriorTotalBasis.ofFn_orderEmb]
  rw [word_ofFn]
  unfold orderedWord enumeration
  congr 1

#print axioms enumeration
#print axioms permutation
#print axioms orderedWord
#print axioms orientation
#print axioms orderedWord_change
#print axioms orderedWord_sorted

end Verification.OrientationWords
