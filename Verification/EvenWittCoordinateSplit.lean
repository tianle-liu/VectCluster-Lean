/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenWittColumns
import Verification.BinaryCoordinateSplit

/-!
# Even Witt Coordinate Split

The even colored quotient is the group ring on the literal remaining
mutable and frozen coordinates. Selected normals and colors are removed
using their actual coordinate embedding, retaining the prescribed signs.
-/
noncomputable section
open scoped Classical
namespace Verification.EvenWittCoordinateSplit
open Verification.OriginalWittQuotient Verification.OriginalWittRelationRank
variable {V C : Type*} [Fintype V] [Fintype C]
variable (c : V → C) (I : Finset V)

def selected : (I ⊕ I) → (V ⊕ C) :=
  Sum.elim (fun i => Sum.inl i.val) (fun i => Sum.inr (c i.val))

variable (hc : Function.Injective (fun i : I => c i.val))

include hc in
omit [Fintype V] [Fintype C] in
theorem selected_injective : Function.Injective (selected c I) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj hab))
    | inr b => cases hab
  | inr a =>
    cases b with
    | inl b => cases hab
    | inr b => exact congrArg Sum.inr (hc (Sum.inr.inj hab))

omit [Fintype V] [Fintype C] in
theorem generator (i : I ⊕ I) :
    OriginalWittQuotient.generator (EvenWittColumns.frozenMatrix c) I i =
      Multiplicative.ofAdd (Pi.single (selected c I i) 1) := by
  cases i with
  | inl i => rfl
  | inr i =>
    apply Multiplicative.toAdd.injective
    funext a
    cases a with
    | inl j => simp [OriginalWittQuotient.generator,columnVector,EvenWittColumns.frozenMatrix,selected,Pi.single_apply]
    | inr k => simp [OriginalWittQuotient.generator,columnVector,EvenWittColumns.frozenMatrix,selected,Pi.single_apply,apply_ite,eq_comm]

def splitting : Bits V C ≃ₗ[ZMod 2]
    (((I ⊕ I) → ZMod 2) × (BinaryCoordinateSplit.Complement (selected c I) → ZMod 2)) :=
  BinaryCoordinateSplit.equiv (selected c I) (selected_injective c I hc)

omit [Fintype C] in
theorem splitting_relation (x : (I ⊕ I) → ZMod 2) :
    splitting c I hc (relationMap (EvenWittColumns.frozenMatrix c) I x) = (x,0) := by
  have he : (splitting c I hc).toLinearMap.comp (relationMap (EvenWittColumns.frozenMatrix c) I) =
      LinearMap.inl (ZMod 2) ((I ⊕ I) → ZMod 2)
        (BinaryCoordinateSplit.Complement (selected c I) → ZMod 2) := by
    apply (Pi.basisFun (ZMod 2) (I ⊕ I)).ext
    intro i
    simp only [Pi.basisFun_apply]
    change splitting c I hc (relationMap (EvenWittColumns.frozenMatrix c) I (Pi.single i 1)) = (Pi.single i 1,0)
    rw [relationMap_single,generator]
    convert BinaryCoordinateSplit.single (selected c I) (selected_injective c I hc) i using 1 <;>
      ext a <;> simp [splitting,Pi.single_apply,BinaryCoordinateSplit.left,BinaryCoordinateSplit.right]
  exact LinearMap.congr_fun he x

def equiv : Stratum (EvenWittColumns.frozenMatrix c) I ≃ₐ[ℤ]
    MonoidAlgebra ℤ (Multiplicative (BinaryCoordinateSplit.Complement (selected c I) → ZMod 2)) :=
  BinarySignedFiberCoordinates.quotientEquiv
    (relationMap (EvenWittColumns.frozenMatrix c) I) (OriginalWittStratumFree.signs I)
    (splitting c I hc) (splitting_relation c I hc) _
    (OriginalWittStratumFree.ideal_eq _ _)

omit [Fintype C] in
theorem monomial (m : Bits V C) :
    equiv c I hc (Ideal.Quotient.mk _ (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd m))) =
      algebraMap ℤ _ (BinarySignedFiber.character (OriginalWittStratumFree.signs I)
        (Multiplicative.ofAdd (splitting c I hc m).1) : ℤ) *
      MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd (splitting c I hc m).2) :=
  BinarySignedFiberCoordinates.quotientEquiv_monomial _ _ _ _ _ _ _

def coordinate (a : BinaryCoordinateSplit.Complement (selected c I)) :
    Stratum (EvenWittColumns.frozenMatrix c) I :=
  Ideal.Quotient.mk _ (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd (Pi.single a.val 1)))

omit [Fintype C] in
theorem coordinate_apply (a : BinaryCoordinateSplit.Complement (selected c I)) :
    equiv c I hc (coordinate c I a) =
      MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd (Pi.single a 1)) := by
  have he : splitting c I hc (Pi.single a.val 1) = (0,Pi.single a 1) := by
    convert BinaryCoordinateSplit.outside_single (selected c I) (selected_injective c I hc) a using 1 <;>
      ext b <;> simp [splitting,Pi.single_apply,BinaryCoordinateSplit.left,BinaryCoordinateSplit.right]
  change equiv c I hc (Ideal.Quotient.mk _ _) = _
  rw [monomial,he]
  simp

#print axioms selected
#print axioms selected_injective
#print axioms generator
#print axioms splitting
#print axioms splitting_relation
#print axioms equiv
#print axioms monomial
#print axioms coordinate
#print axioms coordinate_apply
end Verification.EvenWittCoordinateSplit
