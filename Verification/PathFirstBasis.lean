/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualFirstEntries
import Verification.PathEndpointWordRemoval

/-!
# Path First Basis

Every degree-zero or degree-one path basis vector occurs in the literal
empty/singleton cutout, with no unproved exhaustiveness assumption.
-/

namespace Verification.PathFirstBasis

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathNormalizedBasis Verification.PathActualFirstEntries

abbrev Vertex (n : ℕ) := ↥(Finset.Icc 1 n)
abbrev OneSource (B : List Bool → Prop) (n : ℕ) := Vertex n × NormalWord B n
abbrev DegreeIndex (B : List Bool → Prop) (n p : ℕ) := {x : NormalIndex B n // x.1.val.card=p}

def zeroIndex (B : List Bool → Prop) (n : ℕ) (u : NormalWord B (n+2)) : NormalIndex B n :=
  ⟨zeroConfig n,⟨u.val,by rw [zero_length]; exact u.property⟩⟩

def oneIndex (B : List Bool → Prop) (n : ℕ) (v : OneSource B n) : NormalIndex B n :=
  ⟨oneConfig n v.1.val v.1.property,⟨v.2.val,by rw [one_length]; exact v.2.property⟩⟩

def zeroDegree (B : List Bool → Prop) (n : ℕ) (u : NormalWord B (n+2)) : DegreeIndex B n 0 :=
  ⟨zeroIndex B n u,rfl⟩

def oneDegree (B : List Bool → Prop) (n : ℕ) (v : OneSource B n) : DegreeIndex B n 1 :=
  ⟨oneIndex B n v,Finset.card_singleton _⟩

theorem zeroDegree_bijective (B : List Bool → Prop) (n : ℕ) : Function.Bijective (zeroDegree B n) := by
  constructor
  · intro u v h
    apply Subtype.ext
    exact congrArg (fun x : DegreeIndex B n 0 => x.val.2.val) h
  · rintro ⟨⟨I,w⟩,hI⟩
    have he : I=zeroConfig n := Subtype.ext (Finset.card_eq_zero.mp hI)
    subst I
    exact ⟨⟨w.val,w.property.1.trans (zero_length n),w.property.2⟩,rfl⟩

theorem oneDegree_bijective (B : List Bool → Prop) (n : ℕ) : Function.Bijective (oneDegree B n) := by
  constructor
  · intro u v h
    have hj : u.1.val=v.1.val := Finset.singleton_injective
      (congrArg (fun x : DegreeIndex B n 1 => x.val.1.val) h)
    have hw : u.2.val=v.2.val := congrArg (fun x : DegreeIndex B n 1 => x.val.2.val) h
    exact Prod.ext (Subtype.ext hj) (Subtype.ext hw)
  · rintro ⟨⟨I,w⟩,hI⟩
    obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hI
    have hmem : j ∈ I.val := hj ▸ Finset.mem_singleton_self j
    have hbound := I.property.1 hmem
    have he : I=oneConfig n j hbound := Subtype.ext hj
    subst I
    exact ⟨(⟨j,hbound⟩,⟨w.val,w.property.1.trans (one_length n j hbound),w.property.2⟩),rfl⟩

noncomputable def zeroBasisEquiv (B : List Bool → Prop) (n : ℕ) :
    NormalWord B (n+2) ≃ DegreeIndex B n 0 := Equiv.ofBijective _ (zeroDegree_bijective B n)

noncomputable def oneBasisEquiv (B : List Bool → Prop) (n : ℕ) :
    OneSource B n ≃ DegreeIndex B n 1 := Equiv.ofBijective _ (oneDegree_bijective B n)

#print axioms Vertex
#print axioms OneSource
#print axioms DegreeIndex
#print axioms zeroIndex
#print axioms oneIndex
#print axioms zeroDegree
#print axioms oneDegree
#print axioms zeroDegree_bijective
#print axioms oneDegree_bijective
#print axioms zeroBasisEquiv
#print axioms oneBasisEquiv

end Verification.PathFirstBasis
