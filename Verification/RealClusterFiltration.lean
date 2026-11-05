/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualRealStratum
import Mathlib.Topology.Algebra.Order.Field

/-!
# Real Cluster Filtration

The actual real solution space of the original exchange equations,
its open zero-count filtration, and its exact zero-set fibers.
-/
noncomputable section
namespace Verification.RealClusterFiltration
open Verification.RealExchangeCharacters Verification.AnticliqueSubcolumns
variable {V C : Type} [Fintype V] [Fintype C]

def Point (B : (V ⊕ C) → V → ℤ) :=
  {p : ((V ⊕ C) → ℝ) × (V → ℝ) //
    (∀ c, p.1 (Sum.inr c)≠0) ∧ ∀ v, p.1 (Sum.inl v)*p.2 v=exchange p.1 (fun a => B a v)}

instance pointTopology (B : (V ⊕ C) → V → ℤ) : TopologicalSpace (Point B) :=
  inferInstanceAs (TopologicalSpace {p : ((V ⊕ C) → ℝ) × (V → ℝ) //
    (∀ c, p.1 (Sum.inr c)≠0) ∧ ∀ v, p.1 (Sum.inl v)*p.2 v=exchange p.1 (fun a => B a v)})

def zeroSet (B : (V ⊕ C) → V → ℤ) (p : Point B) : Finset V :=
  Finset.univ.filter (fun v => p.val.1 (Sum.inl v)=0)

theorem mem_zeroSet (B : (V ⊕ C) → V → ℤ) (p : Point B) (v : V) :
    v∈zeroSet B p ↔ p.val.1 (Sum.inl v)=0 := by simp [zeroSet]

theorem coordinate_continuous (B : (V ⊕ C) → V → ℤ) (a : V ⊕ C) :
    Continuous (fun p : Point B => p.val.1 a) :=
  (continuous_apply a).comp (continuous_fst.comp continuous_subtype_val)

def openBy (B : (V ⊕ C) → V → ℤ) (I : Finset V) : Set (Point B) :=
  {p | ∀ v : {v : V // v∉I}, p.val.1 (Sum.inl v.val)≠0}

theorem openBy_isOpen (B : (V ⊕ C) → V → ℤ) (I : Finset V) : IsOpen (openBy B I) := by
  change IsOpen {p : Point B | ∀ v : {v : V // v∉I}, p.val.1 (Sum.inl v.val)≠0}
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite (fun v => (isOpen_ne : IsOpen {x : ℝ | x≠0}).preimage
    (coordinate_continuous B (Sum.inl v.val)))

theorem mem_openBy (B : (V ⊕ C) → V → ℤ) (I : Finset V) (p : Point B) :
    p∈openBy B I ↔ zeroSet B p⊆I := by
  constructor
  · intro h v hv
    by_contra hn
    exact h ⟨v,hn⟩ ((mem_zeroSet B p v).mp hv)
  · intro h v hz
    exact v.property (h ((mem_zeroSet B p v.val).mpr hz))

def omega (B : (V ⊕ C) → V → ℤ) (r : ℕ) : Set (Point B) := {p | (zeroSet B p).card≤r}

theorem omega_eq_union (B : (V ⊕ C) → V → ℤ) (r : ℕ) :
    omega B r=⋃ I : {I : Finset V // I.card≤r}, openBy B I.val := by
  ext p
  constructor
  · intro hp
    apply Set.mem_iUnion.mpr
    exact ⟨⟨zeroSet B p,hp⟩,(mem_openBy B _ p).mpr (Finset.Subset.refl _)⟩
  · intro hp
    obtain ⟨I,hI⟩ := Set.mem_iUnion.mp hp
    exact (Finset.card_le_card ((mem_openBy B I.val p).mp hI)).trans I.property

theorem omega_isOpen (B : (V ⊕ C) → V → ℤ) (r : ℕ) : IsOpen (omega B r) := by
  rw [omega_eq_union]
  exact isOpen_iUnion (fun I => openBy_isOpen B I.val)

theorem omega_mono (B : (V ⊕ C) → V → ℤ) : Monotone (omega B) := by
  intro r s hrs p hp
  exact hp.trans hrs

theorem omega_exhaustive (B : (V ⊕ C) → V → ℤ) : omega B (Fintype.card V)=Set.univ := by
  ext p
  simp only [omega,Set.mem_setOf_eq,Set.mem_univ,iff_true]
  exact Finset.card_le_univ _

theorem successive_level (B : (V ⊕ C) → V → ℤ) (r : ℕ) :
    omega B (r+1)\omega B r={p | (zeroSet B p).card=r+1} := by
  ext p
  simp only [omega,Set.mem_diff,Set.mem_setOf_eq]
  omega

def fiberToStratum (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (p : {p : Point B // zeroSet B p=I}) : ActualRealStratum.Point B I :=
  ⟨p.val.val,by
    refine ⟨?_,?_,p.val.property.2⟩
    · intro i
      exact (mem_zeroSet B p.val i.val).mp (by simpa only [p.property] using i.property)
    · intro a
      cases ha : a.val with
      | inr c => simpa only [ha] using p.val.property.1 c
      | inl v =>
        intro hz
        have hv : v∈I := by rw [← p.property];exact (mem_zeroSet B p.val v).mpr (by simpa only [ha] using hz)
        exact a.property v hv ha⟩

def stratumToFiber (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (p : ActualRealStratum.Point B I) : {p : Point B // zeroSet B p=I} := by
  let q : Point B := ⟨p.val,⟨fun c => p.property.2.1 ⟨Sum.inr c,by simp⟩,p.property.2.2⟩⟩
  refine ⟨q,?_⟩
  ext v
  rw [mem_zeroSet]
  constructor
  · intro hz
    by_contra hn
    exact p.property.2.1 ⟨Sum.inl v,by intro i hi he;exact hn ((Sum.inl.inj he).symm ▸ hi)⟩ hz
  · intro hv
    exact p.property.1 ⟨v,hv⟩

def fiberHomeomorph (B : (V ⊕ C) → V → ℤ) (I : Finset V) :
    {p : Point B // zeroSet B p=I} ≃ₜ ActualRealStratum.Point B I where
  toFun := fiberToStratum B I
  invFun := stratumToFiber B I
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext;rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

#print axioms Point
#print axioms pointTopology
#print axioms zeroSet
#print axioms mem_zeroSet
#print axioms coordinate_continuous
#print axioms openBy
#print axioms openBy_isOpen
#print axioms mem_openBy
#print axioms omega
#print axioms omega_eq_union
#print axioms omega_isOpen
#print axioms omega_mono
#print axioms omega_exhaustive
#print axioms successive_level
#print axioms fiberToStratum
#print axioms stratumToFiber
#print axioms fiberHomeomorph
end Verification.RealClusterFiltration
