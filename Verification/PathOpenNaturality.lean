/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenInsertion

/-!
# Path Open Naturality

Naturality of explicit partner elimination under ring homomorphisms.
-/
namespace Verification.PathOpenNaturality
open Verification.PathPresentation Verification.PathOpenInsertion
variable {A B : Type*} [CommRing A] [CommRing B] {n : ℕ}

theorem map_insertY (f : A →+* B) (a b : A) (u : Aˣ) (xx yy : Fin n → A)
    (i : Fin (n+1)) :
    f (insertY a b u xx yy i) =
      insertY (f a) (f b) (Units.map f.toMonoidHom u) (fun j => f (xx j)) (fun j => f (yy j)) i := by
  induction i using Fin.cases with
  | zero =>
    simp only [insertY, Fin.cons_zero, map_mul, map_add, boundary_map f]
    rfl
  | succ i => rfl

#print axioms map_insertY
end Verification.PathOpenNaturality
