/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedThomSections
import Verification.CoordinatePairReindex
import Mathlib.GroupTheory.Perm.Sign

/-!
# Thom Permutation Input

The ordinary degree theorem for a permutation of the coordinates
of a trivial normal bundle. Only permutations within the same indexed
Thom space occur here; no choice of ordering on different index types
is implicitly identified. The action is the usual quadratic orientation
action on the contracted coefficient sheaf.
-/
noncomputable section
namespace Verification.ThomPermutationInput
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def permutationIso (S ι : Type) [CommRing S] (e : Equiv.Perm ι) :
    LocalizedThomSections.thom G S ι ≅ LocalizedThomSections.thom G S ι :=
  CoordinatePairReindex.relativeIso (MvPolynomial ι S) ι ι MvPolynomial.X e G ≪≫
    CoordinatePairEquiv.relativeIso (MvPolynomial.X ∘ e) MvPolynomial.X
      (MvPolynomial.renameEquiv S e.symm).toRingEquiv
      (fun i => by simp [MvPolynomial.renameEquiv_apply]) G

variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (T : LocalizedThomSections.Standard J L G R site M N)

structure Standard where
  orientation : ∀ (S : Type) [CommRing S] [Algebra R S] (d : ℤ),
    ℤˣ →* Module.End ℤ ((N d).val.obj (Opposite.op (Spec (CommRingCat.of S))))
  permutation : ∀ (S ι : Type) [CommRing S] [Algebra R S] [Fintype ι] [DecidableEq ι]
    (hs : Algebra.Smooth R S) (e : Equiv.Perm ι) (j : ℤ)
    (a : L.obj (LocalizedThomSections.thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(Fintype.card ι : ℤ)) (M j)))),
    T.evaluate S ι hs j (L.map (permutationIso G S ι e).hom ≫ a) =
      orientation S (j-Fintype.card ι) (Equiv.Perm.sign e) (T.evaluate S ι hs j a)

#print axioms permutationIso
#print axioms Standard
end Verification.ThomPermutationInput
