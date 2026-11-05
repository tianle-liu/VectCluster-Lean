/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ThomPermutationInput
import Verification.OrderedFlagNormalCoordinates
import Verification.SelectedNormalOrientation

/-!
# Ordered Flag Thom Degree

The actual insertion permutation acts by the indicated power of
the quadratic orientation involution. This uses only the uniform degree
degree result for same-index Thom permutations; the flag permutation and its
coordinate factorization are proved independently.
-/
noncomputable section
namespace Verification.OrderedFlagThomDegree
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
variable (S ι : Type) [CommRing S] [Algebra R S] [Fintype ι] [LinearOrder ι]
variable (hs : Algebra.Smooth R S) (v : ι) (j : ℤ)

omit [J.Additive] [L.Additive] in
theorem insertion_evaluation
    (a : L.obj (LocalizedThomSections.thom G S (Fin (OrderedFlagNormalCoordinates.count ι v))) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single
        (-(Fintype.card (Fin (OrderedFlagNormalCoordinates.count ι v)) : ℤ)) (M j)))) :
    T.evaluate S (Fin (OrderedFlagNormalCoordinates.count ι v)) hs j
      (L.map (ThomPermutationInput.permutationIso G S _ (OrderedFlagNormalCoordinates.insertion ι v)).hom ≫ a) =
    (O.orientation S (j-Fintype.card (Fin (OrderedFlagNormalCoordinates.count ι v))) (-1) ^
      ((Finset.univ.erase v).filter (fun i : ι => i < v)).card)
      (T.evaluate S (Fin (OrderedFlagNormalCoordinates.count ι v)) hs j a) := by
  rw [O.permutation,OrderedFlagNormalCoordinates.insertion_sign,map_pow]

omit [J.Additive] [L.Additive] in
theorem inverse_insertion_evaluation
    (a : L.obj (LocalizedThomSections.thom G S (Fin (OrderedFlagNormalCoordinates.count ι v))) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single
        (-(Fintype.card (Fin (OrderedFlagNormalCoordinates.count ι v)) : ℤ)) (M j)))) :
    T.evaluate S (Fin (OrderedFlagNormalCoordinates.count ι v)) hs j
      (L.map (ThomPermutationInput.permutationIso G S _ (OrderedFlagNormalCoordinates.insertion ι v).symm).hom ≫ a) =
    (O.orientation S (j-Fintype.card (Fin (OrderedFlagNormalCoordinates.count ι v))) (-1) ^
      ((Finset.univ.erase v).filter (fun i : ι => i < v)).card)
      (T.evaluate S (Fin (OrderedFlagNormalCoordinates.count ι v)) hs j a) := by
  rw [O.permutation,Equiv.Perm.sign_symm,OrderedFlagNormalCoordinates.insertion_sign,map_pow]

variable {V : Type} [LinearOrder V] (K : Finset V) (vK : K)

theorem selected_sign :
    Equiv.Perm.sign (OrderedFlagNormalCoordinates.insertion K vK) =
      (-1) ^ ((K.erase vK.val).filter (fun i : V => i < vK.val)).card := by
  rw [OrderedFlagNormalCoordinates.insertion_sign]
  rw [show ((OrderedFlagNormalCoordinates.oldSet K vK).filter (fun i : K => i < vK)).card =
    ((K.erase vK.val).filter (fun i : V => i < vK.val)).card from SelectedNormalOrientation.below_card K vK]

#print axioms insertion_evaluation
#print axioms inverse_insertion_evaluation
#print axioms selected_sign
end Verification.OrderedFlagThomDegree
