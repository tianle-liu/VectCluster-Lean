/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ThomPermutationNaturality

/-!
# Orientation Base Naturality

Naturality of the quadratic sign action is forced by the ordinary
degree of the transposition of two normal coordinates and the already
proved permutation/base-change square. It is not an added input.
-/
noncomputable section
namespace Verification.OrientationBaseNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (O : ThomPermutationInput.Standard J L G R site M N V)
variable (g : S →ₐ[R] T) (hs : Algebra.Smooth R S) (ht : Algebra.Smooth R T)

include hV hs ht in
omit [J.Additive] [L.Additive] in
theorem negative_naturality (d : ℤ)
    (a : (N d).val.obj (Opposite.op (Spec (CommRingCat.of S)))) :
    (N d).val.map (Spec.map (CommRingCat.ofHom g.toRingHom)).op
      (O.orientation S d (-1) a) =
    O.orientation T d (-1)
      ((N d).val.map (Spec.map (CommRingCat.ofHom g.toRingHom)).op a) := by
  have h := ThomPermutationNaturality.orientation_sign_naturality (Fin 2) (Equiv.swap 0 1)
    J L G R site M N V hV O g hs ht (d+2)
  rw [Fintype.card_fin] at h
  rw [show (d+2-((2:ℕ):ℤ))=d by omega] at h
  simp only [Equiv.Perm.sign_swap (show (0:Fin 2)≠1 by decide)] at h
  exact h a

include hV hs ht in
omit [J.Additive] [L.Additive] in
theorem power_naturality (d : ℤ) (p : ℕ)
    (a : (N d).val.obj (Opposite.op (Spec (CommRingCat.of S)))) :
    (N d).val.map (Spec.map (CommRingCat.ofHom g.toRingHom)).op
      ((O.orientation S d (-1)^p) a) =
    (O.orientation T d (-1)^p)
      ((N d).val.map (Spec.map (CommRingCat.ofHom g.toRingHom)).op a) := by
  induction p generalizing a with
  | zero => rfl
  | succ p ih =>
    simp only [pow_succ,Module.End.mul_apply]
    rw [ih,negative_naturality J L G R S T site M N V hV O g hs ht d]

#print axioms negative_naturality
#print axioms power_naturality
end Verification.OrientationBaseNaturality
