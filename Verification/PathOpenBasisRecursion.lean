/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathClosedBasisRecursion
import Verification.PathNormalWordRecursion

/-!
# Path Open Basis Recursion

Complete actual open-part basis recursion: Z carries the old endpoint's
two-element torus factor, whereas Y has a fixed initial endpoint.
-/

namespace Verification.PathOpenBasisRecursion

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathEndpointWords Verification.PathNormalizedBasis
  Verification.PathFirstVertexSupport Verification.PathConfigRecursion
  Verification.PathNormalWordRecursion

theorem open_free_count (n : ℕ) (I : OpenConfig n) :
    (available I.val.val (n+1+2)).card=(available (openEquiv n I).val (n+2)).card+1 := by
  have ho := available_card I.val.property
  have hn := available_card (openEquiv n I).property
  have hc := open_card n I
  omega

theorem open_tail_positive (n : ℕ) (I : OpenConfig n) :
    0 < (available (openEquiv n I).val (n+2)).card :=
  Finset.card_pos.mpr ⟨0,zero_available (openEquiv n I).property (by omega)⟩

noncomputable def openRegroup (B : List Bool → Prop) (n : ℕ) :
    OpenIndex B (n+1) ≃ Σ I : OpenConfig n, NormalWord B (available I.val.val (n+1+2)).card where
  toFun x := ⟨⟨x.val.1,x.property⟩,x.val.2⟩
  invFun x := ⟨⟨x.1.val,x.2⟩,x.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def lengthEquiv (B : List Bool → Prop) (n : ℕ) (I : OpenConfig n) :
    NormalWord B (available I.val.val (n+1+2)).card ≃
      NormalWord B ((available (openEquiv n I).val (n+2)).card+1) :=
  Equiv.subtypeEquivRight (fun _ => by rw [open_free_count n I])

noncomputable def zFiberEquiv (n : ℕ) (I : OpenConfig n) :
    NormalWord RightNormal (available I.val.val (n+1+2)).card ≃
      Bool × NormalWord RightNormal (available (openEquiv n I).val (n+2)).card :=
  (lengthEquiv RightNormal n I).trans (rightEquiv _ (open_tail_positive n I))

noncomputable def yFiberEquiv (n : ℕ) (I : OpenConfig n) :
    NormalWord BothNormal (available I.val.val (n+1+2)).card ≃
      NormalWord RightNormal (available (openEquiv n I).val (n+2)).card :=
  (lengthEquiv BothNormal n I).trans (bothEquiv _ (open_tail_positive n I))

/-- Move the actual free endpoint bit outside the shorter path's complete basis. -/
noncomputable def torusRegroup (B : List Bool → Prop) (n : ℕ) :
    (Σ I : Config n, Bool × NormalWord B (available I.val (n+2)).card) ≃
      Bool × NormalIndex B n where
  toFun x := (x.2.1,⟨x.1,x.2.2⟩)
  invFun x := ⟨x.2.1,x.1,x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The complete Z open basis is exactly a shorter Z basis times a torus basis. -/
noncomputable def zOpenIndexEquiv (n : ℕ) :
    OpenIndex RightNormal (n+1) ≃ Bool × NormalIndex RightNormal n :=
  ((openRegroup RightNormal n).trans
    (Equiv.sigmaCongr (openEquiv n) (zFiberEquiv n))).trans (torusRegroup RightNormal n)

/-- The complete Y open basis is exactly the shorter Z basis. -/
noncomputable def yOpenIndexEquiv (n : ℕ) : OpenIndex BothNormal (n+1) ≃ NormalIndex RightNormal n :=
  (openRegroup BothNormal n).trans (Equiv.sigmaCongr (openEquiv n) (yFiberEquiv n))

theorem zOpenIndexEquiv_config (n : ℕ) (x : OpenIndex RightNormal (n+1)) :
    (zOpenIndexEquiv n x).2.1=openEquiv n ⟨x.val.1,x.property⟩ := rfl

theorem yOpenIndexEquiv_config (n : ℕ) (x : OpenIndex BothNormal (n+1)) :
    (yOpenIndexEquiv n x).1=openEquiv n ⟨x.val.1,x.property⟩ := rfl

theorem zOpenIndexEquiv_word (n : ℕ) (x : OpenIndex RightNormal (n+1)) :
    (zOpenIndexEquiv n x).2.2.val=x.val.2.val.tail := rfl

theorem yOpenIndexEquiv_word (n : ℕ) (x : OpenIndex BothNormal (n+1)) :
    (yOpenIndexEquiv n x).2.val=x.val.2.val.tail := rfl

#print axioms open_free_count
#print axioms open_tail_positive
#print axioms openRegroup
#print axioms lengthEquiv
#print axioms zFiberEquiv
#print axioms yFiberEquiv
#print axioms torusRegroup
#print axioms zOpenIndexEquiv
#print axioms yOpenIndexEquiv
#print axioms zOpenIndexEquiv_config
#print axioms yOpenIndexEquiv_config
#print axioms zOpenIndexEquiv_word
#print axioms yOpenIndexEquiv_word

end Verification.PathOpenBasisRecursion
