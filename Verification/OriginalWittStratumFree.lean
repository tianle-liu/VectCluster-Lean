/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittRelationRank
import Verification.BinarySignedFiber
import Mathlib.FieldTheory.Finiteness

/-!
# Original Witt Stratum Free

The literal integer Witt stratum quotient is a finite free abelian group
of the manuscript's rank. Its complementary group algebra is constructed
from the original relation vectors, not supplied as a geometric assumption.
-/
noncomputable section
open scoped Classical
namespace Verification.OriginalWittStratumFree
open Verification.OriginalWittQuotient Verification.OriginalWittRelationRank
open Verification.AnticliqueSubcolumns
variable {V C : Type*} [Fintype V] [Fintype C]

def signs (I : Finset V) : I ⊕ I → ℤˣ := Sum.elim (fun _ => 1) (fun _ => -1)

omit [Fintype V] in
theorem signs_val (I : Finset V) (i : I ⊕ I) : (signs I i : ℤ) = generatorSign I i := by
  cases i <;> rfl

omit [Fintype V] [Fintype C] in
theorem ideal_eq (B : (V ⊕ C) → V → ℤ) (I : Finset V) :
    relationIdeal B I = BinarySignedFiber.prescribedIdeal (relationMap B I) (signs I) := by
  unfold relationIdeal SignedGroupRingFace.relations BinarySignedFiber.prescribedIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  simp only [SignedGroupRingFace.relation,signs_val]
  have hh : relationMap B I (Pi.single i 1) = Multiplicative.toAdd (generator B I i) :=
    relationMap_single B I i
  convert congrArg (fun a : Bits V C => MonoidAlgebra.of ℤ (Group V C)
    (Multiplicative.ofAdd a) - algebraMap ℤ (Ambient V C) (generatorSign I i)) hh.symm using 1
  congr 2
  apply congrArg Multiplicative.ofAdd
  apply congrArg (relationMap B I)
  funext j
  simp [Pi.single_apply]

abbrev QuotientBits (B : (V ⊕ C) → V → ℤ) (I : Finset V) :=
  Bits V C ⧸ LinearMap.range (relationMap B I)

def groupAlgebraEquiv (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (hz : ∀ i j : I, B (Sum.inl j.val) i.val = 0) (hAS : AS B I) :
    Stratum B I ≃ₐ[ℤ] MonoidAlgebra ℤ (Multiplicative (QuotientBits B I)) :=
  (Ideal.quotientEquivAlgOfEq ℤ (ideal_eq B I)).trans
    (BinarySignedFiber.primitiveFiberEquiv (relationMap B I)
      (relationMap_injective B I hz hAS) (signs I))

def basis (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (hz : ∀ i j : I, B (Sum.inl j.val) i.val = 0) (hAS : AS B I) :
    Basis (Multiplicative (QuotientBits B I)) ℤ (Stratum B I) :=
  Finsupp.basisSingleOne.map (groupAlgebraEquiv B I hz hAS).symm.toLinearEquiv

theorem free (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (hz : ∀ i j : I, B (Sum.inl j.val) i.val = 0) (hAS : AS B I) :
    Module.Free ℤ (Stratum B I) := Module.Free.of_basis (basis B I hz hAS)

theorem finite (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (hz : ∀ i j : I, B (Sum.inl j.val) i.val = 0) (hAS : AS B I) :
    Module.Finite ℤ (Stratum B I) := Module.Finite.of_basis (basis B I hz hAS)

theorem rank (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (hz : ∀ i j : I, B (Sum.inl j.val) i.val = 0) (hAS : AS B I) :
    Module.finrank ℤ (Stratum B I) =
      2^(Fintype.card V + Fintype.card C - 2*I.card) := by
  letI : Fintype (QuotientBits B I) := Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis (basis B I hz hAS)]
  rw [Fintype.card_congr (Multiplicative.toAdd : Multiplicative (QuotientBits B I) ≃ QuotientBits B I)]
  rw [Module.card_eq_pow_finrank (K := ZMod 2),ZMod.card,quotient_dimension B I hz hAS]

#print axioms signs
#print axioms signs_val
#print axioms ideal_eq
#print axioms QuotientBits
#print axioms groupAlgebraEquiv
#print axioms basis
#print axioms free
#print axioms finite
#print axioms rank
end Verification.OriginalWittStratumFree
