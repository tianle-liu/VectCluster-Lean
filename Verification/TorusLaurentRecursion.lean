/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SingleLaurentGroupAlgebra
import Verification.TorusZero
import Verification.TorusSmooth
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Torus Laurent Recursion

Explicitly peel one Laurent coordinate from the character group algebra.
-/
noncomputable section
namespace Verification.TorusLaurentRecursion

def functionSplit (n : ℕ) : (Fin (n+1) → ℤ) ≃ₗ[ℤ] (ℤ × (Fin n → ℤ)) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv x := by cases x; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def latticeSplit (n : ℕ) : (Fin (n+1) →₀ ℤ) ≃ₗ[ℤ] (ℤ × (Fin n →₀ ℤ)) :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin (n+1))).trans
    ((functionSplit n).trans ((LinearEquiv.refl ℤ ℤ).prodCongr
      (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).symm))

variable (R : Type) [CommRing R]

def successorEquiv (n : ℕ) : OriginalTorus.Torus R (Fin (n+1)) ≃ₐ[R]
    SingleLaurent.Laurent.{0,0} (OriginalTorus.Torus R (Fin n)) :=
  ((MonoidAlgebra.domCongr R R (PrimitiveCharacters.groupSplitting (latticeSplit n))).trans
    (ProductTorusAlgebra.equiv R (Multiplicative ℤ) (Multiplicative (Fin n →₀ ℤ)))).trans
      ((SingleLaurentGroupAlgebra.equiv (OriginalTorus.Torus R (Fin n))).symm.restrictScalars R)

#print axioms functionSplit
#print axioms latticeSplit
#print axioms successorEquiv
end Verification.TorusLaurentRecursion
