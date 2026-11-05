/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathStratumRingUniversal
import Verification.OriginalStratumUniversal

/-!
# Path Original Stratum Transport

The literal path layer and the original global zero layer are the same
quotient/localization whenever the actual ambient ring equivalence preserves
original coordinates. The endpoint-unit conditions are the literal Y/Z ones.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
namespace Verification.PathOriginalStratumTransport
open Verification.PathPresentation Verification.PathLiteralStratum
open Verification.PathCompression Verification.PathClassRepresentatives
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.IndependentBasicOpen Verification.GlobalNormalFrame
open Finset
open scoped BigOperators

variable (n : ℕ) (I : Finset ℕ)
def mutableSet : Finset (Fin n) := univ.filter (fun i => i.val+1∈I)

theorem mem_mutableSet (i : Fin n) : i∈mutableSet n I ↔ i.val+1∈I := by simp [mutableSet]

variable {n I} (hI : Admissible n I)
theorem mutableIndex_mem (i : I) : mutableIndex hI i ∈ mutableSet n I := by
  rw [mem_mutableSet]
  have hi := (mem_Icc.mp (hI.1 i.property)).1
  simpa only [mutableIndex,show i.val-1+1=i.val by omega] using i.property

variable (R S κ : Type) [CommRing R] [CommRing S] [Fintype κ]
variable (a b : R) (ha : IsUnit a) (hb : IsUnit b)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (e : PathAlgebra n a b ≃+* Global S κ n B)
variable (he : ∀ i,e (x a b i)=initial S κ n B (Sum.inl i))
local notation "F" => mutableSet n I
local notation "Target" => ZeroLayer S κ n (mutableSet n I) B

def forwardBase : PathAlgebra n a b →+* Target :=
  (OriginalStratumUniversal.baseMap S κ n (mutableSet n I) B).comp e.toRingHom

include he in
theorem forwardBase_zero (i : I) : forwardBase (I := I) R S κ a b B e (x a b (mutableIndex hI i))=0 := by
  change OriginalStratumUniversal.baseMap S κ n (mutableSet n I) B (e _)=0
  rw [he]
  exact OriginalStratumUniversal.selected_zero S κ n (mutableSet n I) B ⟨_,mutableIndex_mem hI i⟩

theorem target_unit (i : Fin n) (hi : i∉mutableSet n I) :
    IsUnit (OriginalStratumUniversal.baseMap S κ n (mutableSet n I) B (initial S κ n B (Sum.inl i))) :=
  (IndependentBasicOpen.complement_units S κ n (mutableSet n I) B (Sum.inl ⟨i,hi⟩)).map
    (Ideal.Quotient.mk (GlobalNormalFrame.zeroIdeal S κ n (mutableSet n I) B))

include ha hb he in
theorem forwardBase_units (p : Vertices n I) :
    IsUnit (forwardBase (I := I) R S κ a b B e
      (PathStratumRingUniversal.pathPosition R a b (vertexPosition p))) := by
  have hp := mem_range.mp (mem_sdiff.mp p.property).1
  have hn := (mem_sdiff.mp p.property).2
  by_cases h₀ : p.val=0
  · have heq : vertexPosition p=0 := Fin.ext h₀
    rw [heq,PathStratumRingUniversal.pathPosition,boundary_zero]
    exact (ha.map (algebraMap R (PathAlgebra n a b))).map (forwardBase (I := I) R S κ a b B e)
  by_cases h₁ : p.val=n+1
  · have heq : vertexPosition p=Fin.last (n+1) := Fin.ext h₁
    rw [heq,PathStratumRingUniversal.pathPosition,boundary_last]
    exact (hb.map (algebraMap R (PathAlgebra n a b))).map (forwardBase (I := I) R S κ a b B e)
  · let i : Fin n := ⟨p.val-1,by omega⟩
    have heq : vertexPosition p=i.castSucc.succ := by apply Fin.ext;dsimp [vertexPosition,i];omega
    rw [heq,PathStratumRingUniversal.pathPosition,boundary_middle]
    change IsUnit (OriginalStratumUniversal.baseMap S κ n (mutableSet n I) B (e (x a b i)))
    rw [he]
    apply target_unit S κ B i
    rw [mem_mutableSet]
    simpa only [i,show p.val-1+1=p.val by omega] using hn

def toOriginal : Layer R hI a b →+* Target :=
  PathStratumRingUniversal.lift R hI a b (forwardBase (I := I) R S κ a b B e)
    (forwardBase_zero hI R S κ a b B e he) (forwardBase_units R S κ a b ha hb B e he)

theorem toOriginal_base (z : PathAlgebra n a b) :
    toOriginal hI R S κ a b ha hb B e he (PathStratumRingUniversal.baseMap R hI a b z)=
      OriginalStratumUniversal.baseMap S κ n (mutableSet n I) B (e z) :=
  PathStratumRingUniversal.lift_base R hI a b _ _ _ z

def backwardBase : Global S κ n B →+* Layer R hI a b :=
  (PathStratumRingUniversal.baseMap R hI a b).comp e.symm.toRingHom

include he in
theorem backwardBase_initial (i : Fin n) : backwardBase hI R S κ a b B e
    (initial S κ n B (Sum.inl i))=layerX R hI a b i := by
  rw [← he i]
  change PathStratumRingUniversal.baseMap R hI a b (e.symm (e (x a b i)))=_
  rw [RingEquiv.symm_apply_apply]
  rfl

include he in
theorem backwardBase_zero (i : Selected n (mutableSet n I)) :
    backwardBase hI R S κ a b B e (initial S κ n B (Sum.inl i.val))=0 := by
  rw [backwardBase_initial hI R S κ a b B e he]
  have hi := (mem_mutableSet n I i.val).mp i.property
  let k : I := ⟨i.val.val+1,hi⟩
  have hk : mutableIndex hI k=i.val := by apply Fin.ext;simp [mutableIndex,k]
  rw [← hk,layer_zero]

include he in
theorem backwardBase_units : IsUnit (backwardBase hI R S κ a b B e (chartValue S κ n (mutableSet n I) B)) := by
  change IsUnit (backwardBase hI R S κ a b B e (∏ i ∈ (mutableSet n I)ᶜ,initial S κ n B (Sum.inl i)))
  rw [map_prod]
  apply IsUnit.prod_iff.mpr
  intro i hi
  rw [backwardBase_initial hI R S κ a b B e he]
  have hn : i.val+1∉I := by simpa only [mem_compl,mem_mutableSet] using hi
  let p : Vertices n I := ⟨i.val+1,mem_sdiff.mpr ⟨mem_range.mpr (by omega),hn⟩⟩
  have hp : vertexPosition p=i.castSucc.succ := by apply Fin.ext;rfl
  have hu := coordinate_isUnit R hI a b p
  rw [hp,position_middle] at hu
  exact hu

def fromOriginal : Target →+* Layer R hI a b :=
  OriginalStratumUniversal.lift S κ n (mutableSet n I) B (backwardBase hI R S κ a b B e)
    (backwardBase_units hI R S κ a b B e he) (backwardBase_zero hI R S κ a b B e he)

theorem fromOriginal_base (z : Global S κ n B) :
    fromOriginal hI R S κ a b B e he (OriginalStratumUniversal.baseMap S κ n (mutableSet n I) B z)=
      PathStratumRingUniversal.baseMap R hI a b (e.symm z) :=
  OriginalStratumUniversal.lift_base S κ n (mutableSet n I) B _ _ _ z

theorem left_inverse : (fromOriginal hI R S κ a b B e he).comp
    (toOriginal hI R S κ a b ha hb B e he)=RingHom.id _ := by
  apply PathStratumRingUniversal.hom_ext R hI a b
  apply RingHom.ext
  intro z
  change fromOriginal hI R S κ a b B e he
    (toOriginal hI R S κ a b ha hb B e he (PathStratumRingUniversal.baseMap R hI a b z))=_
  rw [toOriginal_base,fromOriginal_base,RingEquiv.symm_apply_apply]
  rfl

theorem right_inverse : (toOriginal hI R S κ a b ha hb B e he).comp
    (fromOriginal hI R S κ a b B e he)=RingHom.id _ := by
  apply OriginalStratumUniversal.hom_ext S κ n (mutableSet n I) B
  apply RingHom.ext
  intro z
  change toOriginal hI R S κ a b ha hb B e he
    (fromOriginal hI R S κ a b B e he (OriginalStratumUniversal.baseMap S κ n (mutableSet n I) B z))=_
  rw [fromOriginal_base,toOriginal_base,RingEquiv.apply_symm_apply]
  rfl

def equiv : Layer R hI a b ≃+* Target :=
  { toOriginal hI R S κ a b ha hb B e he with
    invFun := fromOriginal hI R S κ a b B e he
    left_inv z := DFunLike.congr_fun (left_inverse hI R S κ a b ha hb B e he) z
    right_inv z := DFunLike.congr_fun (right_inverse hI R S κ a b ha hb B e he) z }

theorem equiv_x (i : Fin n) : equiv hI R S κ a b ha hb B e he (layerX R hI a b i)=
    OriginalStratumUniversal.baseMap S κ n (mutableSet n I) B (initial S κ n B (Sum.inl i)) := by
  change toOriginal hI R S κ a b ha hb B e he (PathStratumRingUniversal.baseMap R hI a b (x a b i))=_
  rw [toOriginal_base,he]

#print axioms mutableSet
#print axioms mem_mutableSet
#print axioms mutableIndex_mem
#print axioms forwardBase
#print axioms forwardBase_zero
#print axioms target_unit
#print axioms forwardBase_units
#print axioms toOriginal
#print axioms toOriginal_base
#print axioms backwardBase
#print axioms backwardBase_initial
#print axioms backwardBase_zero
#print axioms backwardBase_units
#print axioms fromOriginal
#print axioms fromOriginal_base
#print axioms left_inverse
#print axioms right_inverse
#print axioms equiv
#print axioms equiv_x
end Verification.PathOriginalStratumTransport
