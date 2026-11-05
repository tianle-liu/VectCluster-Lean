/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualScalarNormalization
import Verification.EmptyColumnRetraction
import Verification.PathForestOriginalRFR

/-!
# Path Forest Scalar Normalization

The path-forest AS hypothesis constructs the required integer splitting
and hence normalizes all scalar coefficients on the actual original global
exchange algebra. No RFR, torus lift, or normalization is a new hypothesis.
-/
noncomputable section
namespace Verification.PathForestScalarNormalization
open Verification.PathForestMatching Verification.PathForestFullRank
variable (R : Type) [CommRing R]
variable {S κ : Type} [Fintype S] [Fintype κ]
variable (m : S → ℕ) (o : S → Bool)
variable (u : (s : S) → largeIndex (m s) (o s) → ℤˣ) (v : (s : S) → Fin (m s) → ℤˣ)
variable (n : ℕ) (e : (PIndex m o ⊕ QIndex m) ≃ Fin n)
variable (B : Matrix (Fin n ⊕ κ) (Fin n ⊕ Empty) ℤ)
variable (hprincipal : ∀ i j,B (Sum.inl (e i)) (Sum.inl (e j))=principal m o u v i j)
variable (hAS : ∀ I,ExchangeReindex.PrincipalIndependent (EmptyColumnRetraction.cut B) I →
  AnticliqueSubcolumns.AS (EmptyColumnRetraction.cut B) I)

def retraction : ((Fin n ⊕ κ) → ℤ) →ₗ[ℤ] ((Fin n ⊕ Empty) → ℤ) :=
  EmptyColumnRetraction.retraction
    (PathForestOriginalRFR.retraction m o u v e (EmptyColumnRetraction.cut B) hprincipal hAS)

theorem left : (retraction m o u v n e B hprincipal hAS).comp B.mulVecLin=LinearMap.id :=
  EmptyColumnRetraction.left B _
    (PathForestOriginalRFR.left m o u v e (EmptyColumnRetraction.cut B) hprincipal hAS)

def globalEquiv (a b : Fin n → Rˣ) : ScalarFrozenGlobal.Global R κ n B a b ≃ₐ[R]
    ScalarFrozenGlobal.Global R κ n B (fun _=>1) (fun _=>1) :=
  ActualScalarNormalization.globalEquiv R κ n B (retraction m o u v n e B hprincipal hAS)
    (left m o u v n e B hprincipal hAS) a b

theorem global_original (a b : Fin n → Rˣ) (r : Fin n ⊕ κ) :
    globalEquiv R m o u v n e B hprincipal hAS a b (ScalarFrozenGlobal.initial R κ n B a b r)=
      algebraMap R _ (ActualScalarNormalization.constants R κ n
        (retraction m o u v n e B hprincipal hAS) a b r : R)*
          ScalarFrozenGlobal.initial R κ n B (fun _=>1) (fun _=>1) r :=
  ActualScalarNormalization.global_original R κ n B (retraction m o u v n e B hprincipal hAS)
    (left m o u v n e B hprincipal hAS) a b r

#print axioms retraction
#print axioms left
#print axioms globalEquiv
#print axioms global_original
end Verification.PathForestScalarNormalization
