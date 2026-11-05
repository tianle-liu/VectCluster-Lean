/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarFreezingIteration
import Verification.ScalarGlobalNonzerodivisors
import Verification.PrincipalConormal

/-!
# Scalar Divisor Geometry

Smoothness and the displayed normal frame for the whole scalar
boundary divisor. Smoothness follows from its actual closed-freezing
presentation; regularity uses the proved global nonzerodivisor.
-/
noncomputable section
namespace Verification.ScalarDivisorGeometry
open Verification.ScalarFrozenGlobal Verification.ScalarDivisorPresentation
open Verification.FrozenAcyclicCover (earlierWeights laterWeights)
open Verification.ExchangeOpenCover
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
variable (hpos : ∀ r i : Fin n, ¬ r < i → (B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ r i : Fin n, ¬ i < r → (-B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hall : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun q j => B q (Sum.inl j)) I)

include hpos hneg hsupport hall in
omit [Nontrivial R] in
theorem divisor_smooth (v : Fin n) : Algebra.Smooth R (Divisor R κ n B a b v) := by
  obtain ⟨m,r,B',c,_,⟨e⟩,_,hp,hn,hsp,hAS⟩ :=
    ScalarFreezingIteration.closed_scalar_seed R κ n B a b v hpos hneg hsupport hall
  letI := ScalarGlobalSmooth.global_smooth_saturated R (Fin r) m B' c (fun _ => 1) hp hn hsp
    (fun I hI => ((GlobalSelectedColumns.AS_iff (Fin r) m B' I).mpr (hAS I hI)).1)
    (fun I hI => ((GlobalSelectedColumns.AS_iff (Fin r) m B' I).mpr (hAS I hI)).2)
  letI : Algebra.Smooth (Global R (Fin r) m B' c (fun _ => 1))
      (Polynomial (Global R (Fin r) m B' c (fun _ => 1))) := {}
  letI : Algebra.Smooth R (Polynomial (Global R (Fin r) m B' c (fun _ => 1))) :=
    Algebra.Smooth.comp R (Global R (Fin r) m B' c (fun _ => 1)) _
  exact Algebra.Smooth.of_equiv e.symm

def conormalBasis (v : Fin n) : Basis PUnit (Divisor R κ n B a b v)
    (divisorIdeal R κ n B a b v).Cotangent :=
  PrincipalConormal.basis (initial R κ n B a b (Sum.inl v))
    (ScalarGlobalNonzerodivisors.coordinate_regular R κ n B a b hpos hneg hsupport hall v)

theorem conormalBasis_apply (v : Fin n) (u : PUnit) : conormalBasis R κ n B a b hpos hneg hsupport hall v u =
    (divisorIdeal R κ n B a b v).toCotangent
      ⟨initial R κ n B a b (Sum.inl v),Ideal.subset_span (Set.mem_singleton _)⟩ :=
  PrincipalConormal.basis_apply _ _ u

def normalParameter (v : Fin n) : Module.Dual (Divisor R κ n B a b v)
    (divisorIdeal R κ n B a b v).Cotangent :=
  (conormalBasis R κ n B a b hpos hneg hsupport hall v).coord PUnit.unit

theorem normalParameter_apply (v : Fin n) : normalParameter R κ n B a b hpos hneg hsupport hall v
    ((divisorIdeal R κ n B a b v).toCotangent
      ⟨initial R κ n B a b (Sum.inl v),Ideal.subset_span (Set.mem_singleton _)⟩) = 1 := by
  rw [← conormalBasis_apply R κ n B a b hpos hneg hsupport hall v PUnit.unit]
  change ((conormalBasis R κ n B a b hpos hneg hsupport hall v).repr
    (conormalBasis R κ n B a b hpos hneg hsupport hall v PUnit.unit)) PUnit.unit = 1
  rw [Basis.repr_self,Finsupp.single_eq_same]

#print axioms divisor_smooth
#print axioms conormalBasis
#print axioms conormalBasis_apply
#print axioms normalParameter
#print axioms normalParameter_apply
end Verification.ScalarDivisorGeometry
