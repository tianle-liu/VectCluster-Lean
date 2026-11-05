/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedFlagThomFactorization
import Verification.OrderedFlagThomDegree

/-!
# Ordered Flag Thom Action

The genuine flag normal comparison acts on coefficient tests by
the required orientation power when the two explicit ordered frames
are used. This assertion concerns the actual derived comparison, not a
map defined by inserting an orientation factor.
-/
noncomputable section
namespace Verification.OrderedFlagThomAction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.OrderedFlagNormalCoordinates Verification.OrderedFlagThomFactorization
universe w₁ w₂
variable {A₀ C : Type*} [Category A₀] [Abelian A₀] [HasDerivedCategory.{w₁} A₀]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A₀ ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] [LinearOrder ι]
variable (x : ι → A) (v : ι)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A₀) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (T : LocalizedThomSections.Standard J L G R site M N)
variable (O : ThomPermutationInput.Standard J L G R site M N T)
variable (hs : Algebra.Smooth R (CoordinateFlag.ClosedAll A ι x v)) (j : ℤ)
local notation "S" => CoordinateFlag.ClosedAll A ι x v
local notation "F" => Fin (count ι v)

omit [J.Additive] [L.Additive] in
theorem actual_flag_evaluation
    (a : L.obj (LocalizedThomSections.thom G S F) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(Fintype.card F : ℤ)) (M j)))) :
    T.evaluate S F hs j
      (L.map (increasingIso ι v R A x G).inv ≫
        (L.map (FlagNormalCoordinates.thomIso R A ι x v G).hom ≫
          L.map (RelativeProductConeNaturality.derivedIso R S (FlagNormalCoordinates.Normals ι v) G).hom ≫
            L.map (numberingIso ι v R A x G).hom) ≫ a) =
    (O.orientation S (j-Fintype.card F) (-1) ^
      ((Finset.univ.erase v).filter (fun i : ι => i < v)).card)
      (T.evaluate S F hs j a) := by
  have hh := congrArg (fun f => L.map f) (actual_thom_factorization ι v R A x G)
  simp only [Functor.map_comp] at hh
  rw [hh]
  simp only [← Category.assoc]
  rw [← Functor.map_comp,Iso.inv_hom_id,CategoryTheory.Functor.map_id,Category.id_comp]
  exact OrderedFlagThomDegree.inverse_insertion_evaluation J L G R site M N T O S ι hs v j a

#print axioms actual_flag_evaluation
end Verification.OrderedFlagThomAction
