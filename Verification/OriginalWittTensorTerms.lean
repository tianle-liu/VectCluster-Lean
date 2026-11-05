/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WittResidueIndexCongruence
import Verification.ActualCellThom
import Verification.IntegerTensorExtension
import Verification.OriginalWittAdjacentFace
import Verification.ActualGlobalBoundary

/-!
# Original Witt Tensor Terms

Degreewise coordinates on the literal tensor extension of the original
integer Witt complex. The finite-product index is identified with the actual
independent-stratum index, and the differential keeps the original faces.
-/
noncomputable section
open scoped Classical TensorProduct
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalWittTensorTerms
open CategoryTheory
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.OriginalWittIntegerComplex
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (A : Type) [AddCommGroup A]
local notation "F" => Independent (laterWeights κ n B)
local notation "BB" => fun a i => B a (Sum.inl i)

def reindex (p : ℕ) :
    ((I : DegreeIndex F p) → OriginalWittQuotient.Stratum BB I.val.val ⊗[ℤ] A) ≃ₗ[ℤ]
      ((I : ActualCellThom.Index κ n B p) → OriginalWittQuotient.Stratum BB I.val ⊗[ℤ] A) where
  toFun f I := f ⟨⟨I.val,I.property.2⟩,I.property.1⟩
  invFun f I := f ⟨I.val.val,⟨I.property,I.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def termEquiv (p : ℕ) :
    degree BB F p ⊗[ℤ] A ≃ₗ[ℤ]
      ((I : ActualCellThom.Index κ n B p) → OriginalWittQuotient.Stratum BB I.val ⊗[ℤ] A) := by
  letI : Fintype (DegreeIndex F p) := Fintype.ofFinite _
  exact (TensorProduct.comm ℤ _ A).trans
    ((TensorProduct.congr (LinearEquiv.refl ℤ A) (degreeEquiv BB F p)).trans
      ((TensorProduct.piRight ℤ ℤ A (fun I : DegreeIndex F p => OriginalWittQuotient.Stratum BB I.val.val)).trans
        ((LinearEquiv.piCongrRight (fun I : DegreeIndex F p =>
          TensorProduct.comm ℤ A (OriginalWittQuotient.Stratum BB I.val.val))).trans
            (reindex κ n B A p))))

omit [Fintype κ] in
theorem termEquiv_tmul (p : ℕ) (f : degree BB F p) (a : A) (I : ActualCellThom.Index κ n B p) :
    termEquiv κ n B A p (f ⊗ₜ[ℤ] a) I = f.val ⟨I.val,I.property.2⟩ ⊗ₜ[ℤ] a := rfl

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)

def complex : CochainComplex (ModuleCat.{0} ℤ) ℕ :=
  IntegerTensorExtension.complex ℤ A (OriginalWittIntegerModel.complex κ n B hpos hneg hsupport)

omit [Fintype κ] in
theorem differential_tmul (p : ℕ) (f : degree BB F p) (a : A) (J : ActualCellThom.Index κ n B (p+1)) :
    termEquiv κ n B A (p+1) (((complex κ n B A hpos hneg hsupport).d p (p+1)) (f ⊗ₜ[ℤ] a)) J =
      ∑ v : J.val, SubsetProjectionComplex.sign J.val v.val •
        OriginalWittAdjacentFace.integerFace κ n J.val B v hpos hneg hsupport J.property.2 A
          (termEquiv κ n B A p (f ⊗ₜ[ℤ] a) (ActualGlobalBoundary.edgeIndex κ n B p J v)) := by
  letI : DecidableEq (Fin n) := fun a b => LinearOrder.toDecidableEq a b
  change termEquiv κ n B A (p+1)
    (TensorProduct.map ((OriginalWittIntegerModel.complex κ n B hpos hneg hsupport).d p (p+1)).hom
      (LinearMap.id : A →ₗ[ℤ] A) (f ⊗ₜ[ℤ] a)) J = _
  simp only [OriginalWittIntegerModel.complex,OriginalWittIntegerComplex.complex,CochainComplex.of_d,
    TensorProduct.map_tmul,LinearMap.id_apply]
  rw [termEquiv_tmul]
  change (∑ v : J.val, SubsetProjectionComplex.sign J.val v.val •
    OriginalWittQuotient.residue BB (J.val.erase v.val) J.val v.val
      (Finset.erase_subset _ _) (Finset.not_mem_erase _ _)
      (OriginalWittIntegerDifferential.face_column_zero BB F
        (OriginalWittIntegerModel.independent_entries κ n B hpos hneg hsupport) ⟨J.val,J.property.2⟩ v)
      (f.val (OriginalWittIntegerDifferential.predecessor F (OriginalWittIntegerModel.hereditary κ n B)
        ⟨J.val,J.property.2⟩ v))) ⊗ₜ[ℤ] a = _
  rw [TensorProduct.sum_tmul]
  apply Finset.sum_congr rfl
  intro v _
  rw [termEquiv_tmul,OriginalWittAdjacentFace.integerFace,TensorProduct.map_tmul]
  have hdec : (fun a b : Fin n => LinearOrder.toDecidableEq a b) = instDecidableEqFin n := Subsingleton.elim _ _
  simp only [OriginalWittIntegerDifferential.predecessor,this,hdec]
  rw [← TensorProduct.smul_tmul']
  apply congrArg (fun z : OriginalWittQuotient.Stratum BB J.val =>
    SubsetProjectionComplex.sign J.val v.val • (z ⊗ₜ[ℤ] a))
  apply WittResidueIndexCongruence.apply
  exact congrArg (fun d : DecidableEq (Fin n) => @Finset.erase (Fin n) d J.val v.val) (Subsingleton.elim _ _)

#print axioms reindex
#print axioms termEquiv
#print axioms termEquiv_tmul
#print axioms complex
#print axioms differential_tmul
end Verification.OriginalWittTensorTerms
