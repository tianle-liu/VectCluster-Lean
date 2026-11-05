/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RelativeProductNaturality

/-!
# Relative Product Open Naturality

The affine normal-pair identification is natural on the actual punctured
schemes, not just on ambient rings. This fixes the open morphism used by the
relative Thom functor.
-/
noncomputable section
namespace Verification.RelativeProductOpenNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.RelativeProductFunctor Verification.RelativeProductAffine
open Verification.RelativeProductPair Verification.RelativeProductNaturality
variable (R A B ι : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable (f : A →ₐ[R] B)

def coordinateOpenMap := CoordinatePairMap.punctureMap MvPolynomial.X MvPolynomial.X
  (MvPolynomial.map f.toRingHom) (fun i : ι => MvPolynomial.map_X _ i)

theorem product_square : (prod.map (𝟙 (punctured R ι)) (affineMap R A B f)).left ≫ openArrow R A ι =
    openArrow R B ι ≫ (prod.map (𝟙 (normal R ι)) (affineMap R A B f)).left := by
  unfold openArrow
  rw [← Over.comp_left,← Over.comp_left]
  congr 1
  simp only [Limits.prod.map_map,Category.id_comp,Category.comp_id]

theorem open_naturality : (prod.map (𝟙 (punctured R ι)) (affineMap R A B f)).left ≫
    (openIso R A ι).hom = (openIso R B ι).hom ≫ coordinateOpenMap R A B ι f := by
  apply (cancel_mono (CoordinatePurityInput.puncture (MvPolynomial ι A) ι MvPolynomial.X).ι).1
  rw [Category.assoc,← RelativeProductPair.pair_square,← Category.assoc,product_square,Category.assoc,
    ambient_naturality,← Category.assoc,RelativeProductPair.pair_square,Category.assoc]
  rw [Category.assoc]
  congr 1
  exact (CoordinatePairMap.puncture_square MvPolynomial.X MvPolynomial.X
    (MvPolynomial.map f.toRingHom) (fun i : ι => MvPolynomial.map_X _ i))

#print axioms coordinateOpenMap
#print axioms product_square
#print axioms open_naturality
end Verification.RelativeProductOpenNaturality
