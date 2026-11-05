/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StandardThomContractionNormalization
import Verification.LaurentSheafBaseChange

/-!
# Sheaf Contraction Naturality

Ordinary base naturality of the contraction grading. The reference
statement ranges over arbitrary smooth algebras and the genuine Laurent
base-change map; the degree-reindexed version is proved internally.
-/
noncomputable section
namespace Verification.SheafContractionNaturality
open CategoryTheory AlgebraicGeometry Opposite
variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (K : StandardThomContractionNormalization.Grading R site N)

structure Standard : Prop where
  naturality : ∀ (S T : Type) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hs : Algebra.Smooth R S) (ht : Algebra.Smooth R T) (f : S →ₐ[R] T) (q : ℤ)
    (a : (AffineSheafContraction.sheafAtOne R S site N q).ker),
    K.contract T ht q (LaurentSheafBaseChange.kernelMap R S T f site N q a) =
      ActualSheafContractionRestriction.pullback site (N (q-1)) f.toRingHom (K.contract S hs q a)

variable (S T : Type) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (hs : Algebra.Smooth R S) (ht : Algebra.Smooth R T) (f : S →ₐ[R] T)

theorem degreeCast_naturality (q q' : ℤ) (h : q=q')
    (a : (N q).val.obj (op (Spec (CommRingCat.of S)))) :
    StandardThomContractionNormalization.degreeCast site N T q q' h
      (ActualSheafContractionRestriction.pullback site (N q) f.toRingHom a) =
    ActualSheafContractionRestriction.pullback site (N q') f.toRingHom
      (StandardThomContractionNormalization.degreeCast site N S q q' h a) := by
  subst q'
  rfl

theorem lower_naturality (H : Standard R site N K) (r : ℕ) (j : ℤ)
    (a : (AffineSheafContraction.sheafAtOne R S site N (j-r)).ker) :
    StandardThomContractionNormalization.lower R site N K T ht r j
      (LaurentSheafBaseChange.kernelMap R S T f site N (j-r) a) =
    ActualSheafContractionRestriction.pullback site (N (j-(r+1 : ℕ))) f.toRingHom
      (StandardThomContractionNormalization.lower R site N K S hs r j a) := by
  change StandardThomContractionNormalization.degreeCast site N T _ _ _
    (K.contract T ht (j-r) (LaurentSheafBaseChange.kernelMap R S T f site N (j-r) a)) = _
  rw [H.naturality]
  exact degreeCast_naturality R site N S T f _ _ _ _

#print axioms Standard
#print axioms degreeCast_naturality
#print axioms lower_naturality
end Verification.SheafContractionNaturality
