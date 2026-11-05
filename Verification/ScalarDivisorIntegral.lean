/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarGlobalDomain
import Verification.ScalarFreezingIteration

/-!
# Scalar Divisor Integral

Every whole mutable boundary divisor of the actual scalar acyclic AS
ring is integral: its actual closed-freezing presentation is a polynomial
ring over another scalar AS ring. Hence its defining principal ideal is
prime.
-/
noncomputable section
namespace Verification.ScalarDivisorIntegral
open Verification.ScalarFrozenGlobal Verification.ScalarDivisorPresentation
open Verification.FrozenAcyclicCover (earlierWeights laterWeights)
open Verification.ExchangeOpenCover
variable (R κ : Type) [CommRing R] [IsDomain R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
variable (hpos : ∀ r i : Fin n, ¬ r < i → (B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ r i : Fin n, ¬ i < r → (-B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hall : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun q j => B q (Sum.inl j)) I)
include hpos hneg hsupport hall

theorem divisor_domain (v : Fin n) : IsDomain (Divisor R κ n B a b v) := by
  obtain ⟨m,r,B',c,_,⟨e⟩,_,hp,hn,hsp,hAS⟩ :=
    ScalarFreezingIteration.closed_scalar_seed R κ n B a b v hpos hneg hsupport hall
  letI := ScalarGlobalDomain.global_domain R (Fin r) m B' c (fun _ => 1) hp hn hsp hAS
  exact Function.Injective.isDomain e.toRingHom e.injective

theorem divisor_prime (v : Fin n) : (divisorIdeal R κ n B a b v).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).mp
    (divisor_domain R κ n B a b hpos hneg hsupport hall v)

#print axioms divisor_domain
#print axioms divisor_prime
end Verification.ScalarDivisorIntegral
