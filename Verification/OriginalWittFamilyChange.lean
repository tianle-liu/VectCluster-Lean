/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittIntegerComplex

/-!
# Original Witt Family Change

Replacing the allowed-set predicate by a proved equivalent predicate
only reindexes the literal stratum complex.
-/
noncomputable section
namespace Verification.OriginalWittFamilyChange
open CategoryTheory
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder V]
variable (B : (V ⊕ C) → V → ℤ) (F F' : Finset V → Prop)
variable (down : ∀ I J, J⊆I → F I → F J)
variable (down' : ∀ I J, J⊆I → F' I → F' J)
variable (indep : ∀ I, F I → ∀ i∈I, ∀ j∈I, i≠j → B (Sum.inl j) i=0)
variable (indep' : ∀ I, F' I → ∀ i∈I, ∀ j∈I, i≠j → B (Sum.inl j) i=0)

def iso (hF : ∀ I, F I ↔ F' I) :
    OriginalWittIntegerComplex.complex B F down indep ≅
      OriginalWittIntegerComplex.complex B F' down' indep' := by
  have he : F = F' := funext (fun I => propext (hF I))
  subst F'
  exact Iso.refl _

#print axioms iso
end Verification.OriginalWittFamilyChange
