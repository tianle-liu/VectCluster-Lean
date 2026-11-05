/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.NatTensorTFRank
import Verification.GraphTensorCohomology

/-!
# Graph Tensor TF

Torsion-free integral cohomology of the actual induced independence
complex gives its arbitrary-coefficient cohomology as a power.
-/
noncomputable section
open scoped Classical
namespace Verification.GraphTensorTF
attribute [local instance 2000] ModuleCat.isModule
open CategoryTheory
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder V]
variable (G : SimpleGraph V) (c : V → C) (T : Finset V)

def integral : CochainComplex (ModuleCat ℤ) ℕ :=
  GraphBlockComplex.simplexComplex ℤ G c (T,∅)

def free (p : ℕ) : Module.Free ℤ ((integral G c T).X p) :=
  Module.Free.of_equiv (GraphBlockComplex.degreeBasisEquiv ℤ
    (GraphBlockComplex.simplexDegree G c (T,∅)) p).symm

def finite (p : ℕ) : Module.Finite ℤ ((integral G c T).X p) :=
  Module.Finite.equiv (GraphBlockComplex.degreeBasisEquiv ℤ
    (GraphBlockComplex.simplexDegree G c (T,∅)) p).symm

attribute [local instance] free finite

def betti (p : ℕ) : ℕ := Module.finrank ℤ ((integral G c T).homology p)

def coefficientEquiv (A : Type) [AddCommGroup A] (p : ℕ) (hp : 0 < p)
    (hin : NoZeroSMulDivisors ℤ ((integral G c T).homology p))
    (hout : NoZeroSMulDivisors ℤ ((integral G c T).homology (p+1))) :
    (GraphTensorCohomology.simplex G c A (T,∅)).homology p ≃+
      (Fin (betti G c T p) → A) :=
  (NatTensorTFRank.coefficientEquiv (integral G c T) p hp
    (by
      letI : SMul ℤ ((integral G c T).homology p) :=
        (ModuleCat.isModule ((integral G c T).homology p)).toSMul
      constructor
      intro a x hx
      exact hin.eq_zero_or_eq_zero_of_smul_eq_zero
        ((int_smul_eq_zsmul (ModuleCat.isModule ((integral G c T).homology p)) a x).symm.trans hx))
    (by
      letI : SMul ℤ ((integral G c T).homology (p+1)) :=
        (ModuleCat.isModule ((integral G c T).homology (p+1))).toSMul
      constructor
      intro a x hx
      exact hout.eq_zero_or_eq_zero_of_smul_eq_zero
        ((int_smul_eq_zsmul (ModuleCat.isModule ((integral G c T).homology (p+1))) a x).symm.trans hx)) A).toAddEquiv

#print axioms integral
#print axioms free
#print axioms finite
#print axioms betti
#print axioms coefficientEquiv
end Verification.GraphTensorTF
