/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteContractedProduct

/-!
# Finite Monoidal Product Congr

The recursive finite tensor of objects respects actual isomorphisms
of its base and every factor.
-/
noncomputable section
namespace Verification.FiniteMonoidalProductCongr
open CategoryTheory CategoryTheory.MonoidalCategory
variable {A : Type*} [Category A] [MonoidalCategory A]
variable {Z W : A} (b : Z ≅ W)

def iso : ∀ (n : ℕ) (U V : Fin n → A), (∀ i, U i ≅ V i) →
    ((FiniteContractedProduct.survivors (A:=A) Z n U) ≅ (FiniteContractedProduct.survivors (A:=A) W n V))
  | 0,_,_,_=>b
  | n+1,U,V,e=>tensorIso (e 0) (iso n (fun i=>U i.succ) (fun i=>V i.succ) (fun i=>e i.succ))

#print axioms iso
end Verification.FiniteMonoidalProductCongr
