/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenWittCoordinateSplit
import Verification.BinarySignedPfisterBasis

/-!
# Even Witt Pfister Basis

A literal Pfister basis of each even colored quotient. Taking sign
+1 for remaining mutable coordinates and -1 for remaining frozen
coordinates gives precisely the article's x and z=-t basis.
-/
noncomputable section
open scoped Classical BigOperators
namespace Verification.EvenWittPfisterBasis
open Verification.OriginalWittQuotient
variable {V C : Type*} [Fintype V] [Fintype C]
variable (c : V → C) (I : Finset V)
variable (hc : Function.Injective (fun i : I => c i.val))

abbrev Remaining := BinaryCoordinateSplit.Complement (EvenWittCoordinateSplit.selected c I)

def signs : Remaining c I → ℤˣ := fun a => Sum.elim (fun _ => 1) (fun _ => -1) a.val

def basis (u : Remaining c I → ℤˣ) :
    Basis (Finset (Remaining c I)) ℤ (Stratum (EvenWittColumns.frozenMatrix c) I) :=
  (BinarySignedPfisterBasis.basis (Remaining c I) u).map
    (EvenWittCoordinateSplit.equiv c I hc).symm.toLinearEquiv

theorem basis_word (u : Remaining c I → ℤˣ) (A : Finset (Remaining c I)) :
    basis c I hc u A =
      ∏ a ∈ A, ((u a : ℤ) • EvenWittCoordinateSplit.coordinate c I a - 1) := by
  apply (EvenWittCoordinateSplit.equiv c I hc).injective
  rw [basis,Basis.map_apply]
  change EvenWittCoordinateSplit.equiv c I hc
    ((EvenWittCoordinateSplit.equiv c I hc).symm (BinarySignedPfisterBasis.basis (Remaining c I) u A)) = _
  rw [AlgEquiv.apply_symm_apply,BinarySignedPfisterBasis.basis_word,map_prod]
  apply Finset.prod_congr rfl
  intro a _
  rw [map_sub,map_one,map_zsmul,EvenWittCoordinateSplit.coordinate_apply]
  congr 2
  convert congrArg (MonoidAlgebra.of ℤ _) (BinarySignedPfisterBasis.index_singleton (Remaining c I) a) using 1
  congr 1
  apply Multiplicative.toAdd.injective
  funext b
  simp [Pi.single_apply]

#print axioms Remaining
#print axioms signs
#print axioms basis
#print axioms basis_word
end Verification.EvenWittPfisterBasis
