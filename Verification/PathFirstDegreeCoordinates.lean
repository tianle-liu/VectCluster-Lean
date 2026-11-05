/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.DegreeBasisCoordinates
import Verification.PathFirstBoundaryCutout
import Verification.PathFullComplex

/-!
# Path First Degree Coordinates

The manuscript's empty and singleton word bases are literal bases of
homological degrees zero and one of the actual finite path complexes.
-/

namespace Verification.PathFirstDegreeCoordinates

open Verification.PathFirstBasis Verification.PathEndpointWords Verification.PathNormalizedBasis
  Verification.PathStratumGrading Verification.PathFirstBoundaryCutout Verification.PathEndpointWordRemoval
  Verification.GradedPerturbation Verification.DegreeBasisCoordinates

variable {R : Type*} [CommRing R]

noncomputable def negativeDegreeIndex (B : List Bool → Prop) (n p : ℕ) :
    DegreeIndex B n p ≃ {x : NormalIndex B n // -degree x=-(p:ℤ)} :=
  Equiv.subtypeEquivRight (fun x => by change x.1.val.card=p ↔ -(x.1.val.card:ℤ)=-(p:ℤ); omega)

noncomputable def zZeroIndex (n : ℕ) : Verification.PathWords.Word (n+1) ≃
    {x : NormalIndex RightNormal n // -degree x=0} :=
  ((rightWordEquiv (n+1)).symm.trans (zeroBasisEquiv RightNormal n)).trans (negativeDegreeIndex RightNormal n 0)

noncomputable def yZeroIndex (m : ℕ) : Verification.PathWords.Word (2*m) ≃
    {x : NormalIndex BothNormal (2*m) // -degree x=0} :=
  ((bothWordEquiv (2*m)).symm.trans (zeroBasisEquiv BothNormal (2*m))).trans (negativeDegreeIndex BothNormal (2*m) 0)

noncomputable def firstIndex (B : List Bool → Prop) (n : ℕ) : OneSource B n ≃
    {x : NormalIndex B n // -degree x=(-1:ℤ)} :=
  (oneBasisEquiv B n).trans (negativeDegreeIndex B n 1)

theorem zZeroIndex_val (n : ℕ) (w : Verification.PathWords.Word (n+1)) :
    (zZeroIndex n w).val=zeroIndex RightNormal n (zZeroWord n w) := rfl

theorem yZeroIndex_val (m : ℕ) (w : Verification.PathWords.Word (2*m)) :
    (yZeroIndex m w).val=zeroIndex BothNormal (2*m) (yZeroWord m w) := rfl

theorem firstIndex_val (B : List Bool → Prop) (n : ℕ) (v : OneSource B n) :
    (firstIndex B n v).val=oneIndex B n v := rfl

noncomputable def zZeroCoordinates (n : ℕ) :
    degreeModule (R := R) (fun x : NormalIndex RightNormal n => -degree x) 0 ≃ₗ[R]
      (Verification.PathWords.Word (n+1) →₀ R) := basisEquiv _ 0 (zZeroIndex n)

noncomputable def yZeroCoordinates (m : ℕ) :
    degreeModule (R := R) (fun x : NormalIndex BothNormal (2*m) => -degree x) 0 ≃ₗ[R]
      (Verification.PathWords.Word (2*m) →₀ R) := basisEquiv _ 0 (yZeroIndex m)

noncomputable def firstCoordinates (B : List Bool → Prop) (n : ℕ) :
    degreeModule (R := R) (fun x : NormalIndex B n => -degree x) (-1) ≃ₗ[R]
      (OneSource B n →₀ R) := basisEquiv _ (-1) (firstIndex B n)

#print axioms negativeDegreeIndex
#print axioms zZeroIndex
#print axioms yZeroIndex
#print axioms firstIndex
#print axioms zZeroIndex_val
#print axioms yZeroIndex_val
#print axioms firstIndex_val
#print axioms zZeroCoordinates
#print axioms yZeroCoordinates
#print axioms firstCoordinates

end Verification.PathFirstDegreeCoordinates
