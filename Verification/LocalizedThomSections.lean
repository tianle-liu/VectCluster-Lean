/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedCoordinatePurity
import Verification.StrictCellTests
import Verification.RealSheafSignature

/-!
# Localized Thom Sections

Ordinary Thom representability for actual localized normal cones.
The standard input is uniform in smooth affine bases and normal coordinates;
it contains no exchange matrix, cellular model, signature, or boundary law.
Strict and raw categories remain distinct, and no full faithfulness of J is
assumed. Naturality is ordinary pullback in the base with the same normal
coordinates. Its compatibility with a fixed localized purity map is proved.
-/
noncomputable section
namespace Verification.LocalizedThomSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.CoordinatePurityInput
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

def thom (S ι : Type) [CommRing S] : DerivedCategory C :=
  relative (MvPolynomial ι S) ι MvPolynomial.X G

def thomMap {S T ι : Type} [CommRing S] [CommRing T] (f : S →+* T) :
    thom G T ι ⟶ thom G S ι :=
  CoordinatePairMap.relativeMap MvPolynomial.X MvPolynomial.X (MvPolynomial.map f)
    (fun i => MvPolynomial.map_X _ i) G

structure Standard where
  evaluate : ∀ (S ι : Type) [CommRing S] [Algebra R S] [Fintype ι],
    Algebra.Smooth R S → ∀ j : ℤ,
    (L.obj (thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(Fintype.card ι : ℤ)) (M j)))) ≃+
        (N (j-Fintype.card ι)).val.obj (Opposite.op (Spec (CommRingCat.of S)))

variable (T : Standard J L G R site M N)

structure Naturality : Prop where
  base_change : ∀ (S S' ι : Type) [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] [Fintype ι]
    (hs : Algebra.Smooth R S) (hs' : Algebra.Smooth R S') (f : S →ₐ[R] S') (j : ℤ)
    (a : L.obj (thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(Fintype.card ι : ℤ)) (M j)))),
    T.evaluate S' ι hs' j (L.map (thomMap G f.toRingHom) ≫ a) =
      (N (j-Fintype.card ι)).val.map (Spec.map (CommRingCat.ofHom f.toRingHom)).op
        (T.evaluate S ι hs j a)

def closedAlgMap {S S' ι : Type} [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] (x : ι → S) (y : ι → S')
    (f : S →ₐ[R] S') (hf : ∀ i,f (x i)=y i) :
    (S ⧸ ConormalFrame.ideal x) →ₐ[R] (S' ⧸ ConormalFrame.ideal y) where
  __ := CoordinatePairMap.closedMap x y f.toRingHom hf
  commutes' r := by
    change Ideal.Quotient.mk _ (f (algebraMap R S r)) = Ideal.Quotient.mk _ (algebraMap R S' r)
    rw [f.commutes]

def precompose {X Y Z : D} (e : X ≅ Y) : (X ⟶ Z) ≃+ (Y ⟶ Z) where
  toFun f := e.inv ≫ f
  invFun f := e.hom ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp only [Preadditive.comp_add]

variable (P : LocalizedCoordinatePurity.Standard L R G)

def pairEvaluation (S ι : Type) [CommRing S] [Algebra R S] [Fintype ι]
    (x : ι → S) (F : Frame R S ι x) (j : ℤ) :
    (L.obj (relative S ι x G) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(Fintype.card ι : ℤ)) (M j)))) ≃+
        (N (j-Fintype.card ι)).val.obj (Opposite.op (Spec (CommRingCat.of (S ⧸ ConormalFrame.ideal x)))) :=
  (precompose (P.comparison S ι x F)).trans
    (T.evaluate (S ⧸ ConormalFrame.ideal x) ι F.closedSmooth j)

omit [J.Additive] [L.Additive] in
theorem pair_naturality (hT : Naturality J L G R site M N T)
    (hP : LocalizedCoordinatePurity.Naturality L R G P)
    (S S' ι : Type) [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S'] [Fintype ι]
    (x : ι → S) (y : ι → S') (f : S →ₐ[R] S') (hf : ∀ i,f (x i)=y i)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (F : Frame R S ι x) (F' : Frame R S' ι y) (j : ℤ)
    (a : L.obj (relative S ι x G) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(Fintype.card ι : ℤ)) (M j)))) :
    pairEvaluation J L G R site M N T P S' ι y F' j
      (L.map (CoordinatePairMap.relativeMap x y f.toRingHom hf G) ≫ a) =
    (N (j-Fintype.card ι)).val.map
      (Spec.map (CommRingCat.ofHom (closedAlgMap R x y f hf).toRingHom)).op
      (pairEvaluation J L G R site M N T P S ι x F j a) := by
  change T.evaluate _ ι F'.closedSmooth j
    ((P.comparison S' ι y F').inv ≫ (L.map (CoordinatePairMap.relativeMap x y f.toRingHom hf G) ≫ a)) = _
  have hp := hP.open_naturality S S' ι x y f hf F F'
  have hpi : (P.comparison S' ι y F').inv ≫ L.map (CoordinatePairMap.relativeMap x y f.toRingHom hf G) =
      L.map (CoordinatePurityNaturality.normalMap G x y f.toRingHom hf) ≫ (P.comparison S ι x F).inv := by
    apply (cancel_mono (P.comparison S ι x F).hom).1
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rw [hp]
    simp
  rw [← Category.assoc,hpi,Category.assoc]
  exact hT.base_change _ _ ι F.closedSmooth F'.closedSmooth (closedAlgMap R x y f hf) j
    ((P.comparison S ι x F).inv ≫ a)

#print axioms thom
#print axioms thomMap
#print axioms Standard
#print axioms Naturality
#print axioms closedAlgMap
#print axioms precompose
#print axioms pairEvaluation
#print axioms pair_naturality
end Verification.LocalizedThomSections
