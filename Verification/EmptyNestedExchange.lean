/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.NestedExchangeUniversal

/-!
# Empty Nested Exchange

A nested exchange presentation with empty mutable type is its actual
coefficient algebra, over the original ground ring.
-/
noncomputable section
namespace Verification.EmptyNestedExchange
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type*} [IsEmpty ι] (p : ι→MvPolynomial ι S)

def forward : NestedExchangeUniversal.Ring S p →ₐ[R] S :=
  NestedExchangeUniversal.lift R S p (AlgHom.id R S) (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i) (fun i=>isEmptyElim i)

def equiv : NestedExchangeUniversal.Ring S p ≃ₐ[R] S :=
  AlgEquiv.ofAlgHom (forward R S p) (IsScalarTower.toAlgHom R S _)
    (by
      apply AlgHom.ext
      intro s
      change forward R S p (algebraMap S _ s)=s
      rw [forward,NestedExchangeUniversal.lift_coefficient]
      rfl)
    (by
      apply NestedExchangeUniversal.hom_ext
      · intro s
        change algebraMap S _ (forward R S p (algebraMap S _ s))=algebraMap S _ s
        rw [forward,NestedExchangeUniversal.lift_coefficient]
        rfl
      · intro i; exact isEmptyElim i
      · intro i; exact isEmptyElim i)

#print axioms forward
#print axioms equiv
end Verification.EmptyNestedExchange
