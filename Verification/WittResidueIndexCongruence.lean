/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittIntegerDifferential

/-!
# Witt Residue Index Congruence

Transport of an actual quotient residue across equality of its source
finite set. Proof witnesses and independently chosen equality decisions do
not alter the induced map on a dependent coefficient family.
-/
noncomputable section
namespace Verification.WittResidueIndexCongruence
open Verification.OriginalWittQuotient
variable {V C : Type*} (B : (V ⊕ C) → V → ℤ) (F : Finset V → Prop)
variable (f : (I : {I : Finset V // F I}) → Stratum B I.val)

theorem apply (I I' J : Finset V) (j : V) (hI : F I) (hI' : F I')
    (h : I ⊆ J) (h' : I' ⊆ J) (hj : j∉I) (hj' : j∉I')
    (hB : ∀ i : I,B (Sum.inl j) i.val=0) (hB' : ∀ i : I',B (Sum.inl j) i.val=0)
    (he : I=I') :
    residue B I J j h hj hB (f ⟨I,hI⟩)=residue B I' J j h' hj' hB' (f ⟨I',hI'⟩) := by
  subst I'
  rfl

#print axioms apply
end Verification.WittResidueIndexCongruence
