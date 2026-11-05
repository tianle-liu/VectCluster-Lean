/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ThomPermutationInput
import Verification.WittSheafSectionsInput

/-!
# Witt Thom Orientation Input

Uniform ordinary quadratic Thom orientation in Witt coefficients.
The alternating incidence factor is deduced from eta-periodic MW relations.
-/
noncomputable section
namespace Verification.WittThomOrientationInput
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)

variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (T : LocalizedThomSections.Standard J L G R site M N)


variable (O : ThomPermutationInput.Standard J L G R site M N T)
variable (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0})
variable (F : WittSheafSectionsInput.Symbols R W)
variable (E : WittSheafSectionsInput.Comparison R W site N)

structure Normalization : Prop where
  negative : ∀ (S : Type) [CommRing S] [Algebra R S] (hs : Algebra.Smooth R S) (q : ℤ)
    (a : WittSheafSectionsInput.RingSection W S),
    O.orientation S q (-1) (E.sections S hs q a)=
      E.sections S hs q (WittSheafSectionsInput.form R W F S hs (-1)*a)

variable (H : Normalization J L G R site M N T O W F E)
variable (S : Type) [CommRing S] [Algebra R S] (hs : Algebra.Smooth R S) (q : ℤ)

include H hs in
omit [J.Additive] [L.Additive] in
theorem orientation_negative (a : (N q).val.obj (Opposite.op (Spec (CommRingCat.of S)))) :
    O.orientation S q (-1) a = -a := by
  obtain ⟨a,rfl⟩ := (E.sections S hs q).surjective a
  rw [H.negative,WittSheafSectionsInput.form_negative_one,neg_one_mul,map_neg]

include H hs in
omit [J.Additive] [L.Additive] in
theorem orientation_power (ν : ℕ)
    (a : (N q).val.obj (Opposite.op (Spec (CommRingCat.of S)))) :
    (O.orientation S q (-1)^ν) a = ((-1 : ℤ)^ν) • a := by
  induction ν with
  | zero => simp
  | succ ν ih =>
      rw [pow_succ',Module.End.mul_apply,orientation_negative J L G R site M N T O W F E H S hs q,ih]
      rw [pow_succ',mul_smul,neg_one_zsmul]

include H hs in
omit [J.Additive] [L.Additive] in
theorem orientation_coefficient (ν : ℕ) (a : WittSheafSectionsInput.RingSection W S) :
    (O.orientation S q (-1)^ν) (E.sections S hs q a)=
      E.sections S hs q (((-1 : ℤ)^ν) • a) := by
  rw [orientation_power J L G R site M N T O W F E H S hs q,map_zsmul]

#print axioms Normalization
#print axioms orientation_negative
#print axioms orientation_power
#print axioms orientation_coefficient
end Verification.WittThomOrientationInput
