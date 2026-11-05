/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ContractedStrictProductInput

/-!
# Contracted Model Transport

Transport of actual strict contracted models along ambient and ring
isomorphisms, and along an isomorphism of their degree-zero survivors.
-/
noncomputable section
namespace Verification.ContractedModelTransport
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.ContractedStrictProductInput
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) (G : Scheme ⥤ CochainComplex C ℤ)

def ambient {X Y : D} {U : A} (e : X≅Y) (P : ContractedModel J Y U) : ContractedModel J X U where
  model := StrictProjectiveModel.ofIso J e P.model
  upper := P.upper
  contraction := P.contraction

def survivor {X : D} {U V : A} (e : U≅V) (P : ContractedModel J X U) : ContractedModel J X V where
  model := P.model
  upper := P.upper
  contraction := P.contraction.trans (HomotopyEquiv.ofIso
    ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).mapIso e))

def ring {S T : Type} [CommRing S] [CommRing T] (e : S ≃+* T) {U : A}
    (P : ContractedModel J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of T))))) U) :
    ContractedModel J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of S))))) U :=
  ambient J (L.mapIso (DerivedCategory.Q.mapIso (G.mapIso (Scheme.Spec.mapIso e.toCommRingCatIso.symm.op)))) P

#print axioms ambient
#print axioms survivor
#print axioms ring
end Verification.ContractedModelTransport
