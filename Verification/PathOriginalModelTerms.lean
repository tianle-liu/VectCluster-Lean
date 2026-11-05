/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalDegreeTerms
import Verification.PathNormalTermIso
import Verification.OriginalStrictCellTests

/-!
# Path Original Model Terms

The actual original path model has exactly the terms of the contracted
path sheaf model, including its genuine constant integer object.
-/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
namespace Verification.PathOriginalModelTerms
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Verification.StrictProjectiveModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover Verification.IndependentChartIndex
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]

variable (T : StrictLocalizedCells.TorusCells J L G R)
variable [Nontrivial R]

open Verification.PathOriginalIndependence
attribute [local instance] Abelian.hasFiniteBiproducts
variable (Z : A) (M : ℤ → A)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (S : StrictTorusSymbolInput.Standard J L G R T Z M site N W V)
variable (Action : PathGradedCoefficientAction.Action (fun j=>M ((j+1:ℕ):ℤ)))
variable (E : OpenConeExcision.StandardExcision G) (P : LocalizedCoordinatePurity.Standard L R G)
variable (H : ChainRepresentability (A := A))
variable (empty : ∀ X : Scheme,IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))

section Y
variable (a p : ℕ)
local notation "B" => PathOriginalYPresentation.matrix (2*a)
local notation "hf" => fun I hI => (PathOriginalAS.y a I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.y a I hI).2

def yDegree :
    (OriginalPositiveCellular.model J L G R T (Empty) (2*a) B
      (positive_order B y_mutable) (negative_order B y_mutable) (support B y_mutable)
      hf hs E P H empty).complex.X (-(p:ℤ)) ≅
    (PathGradedSheafModel.ySource (fun j:ℕ=>M (j:ℤ)) Action Z a).X (-(p:ℤ)) :=
  OriginalStrictCellTests.degreeIso J L G R T (Empty) (2*a) B
    (positive_order B y_mutable) (negative_order B y_mutable) (support B y_mutable)
    hf hs E P H empty p ≪≫
      PathOriginalDegreeTerms.yLayer J L G R T Z M site N W V S a p ≪≫
        PathNormalTermIso.y Z (fun j:ℕ=>M (j:ℤ)) Action a (-(p:ℤ))
#print axioms yDegree
end Y

section Z
variable (n p : ℕ)
local notation "B" => PathOriginalZPresentation.matrix (n)
local notation "hf" => fun I hI => (PathOriginalAS.z n I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.z n I hI).2

def zDegree :
    (OriginalPositiveCellular.model J L G R T (Fin 1) (n) B
      (positive_order B z_mutable) (negative_order B z_mutable) (support B z_mutable)
      hf hs E P H empty).complex.X (-(p:ℤ)) ≅
    (PathGradedSheafModel.zSource (fun j:ℕ=>M (j:ℤ)) Action Z n).X (-(p:ℤ)) :=
  OriginalStrictCellTests.degreeIso J L G R T (Fin 1) (n) B
    (positive_order B z_mutable) (negative_order B z_mutable) (support B z_mutable)
    hf hs E P H empty p ≪≫
      PathOriginalDegreeTerms.zLayer J L G R T Z M site N W V S n p ≪≫
        PathNormalTermIso.z Z (fun j:ℕ=>M (j:ℤ)) Action n (-(p:ℤ))
#print axioms zDegree
end Z
end Verification.PathOriginalModelTerms
