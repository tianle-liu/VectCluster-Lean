/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathMilnorWittSignedWordFace
import Verification.GradedMilnorWittLaurentWords

/-!
# Graded Milnor Witt Path Column

The full path word column in actual graded Milnor-Witt sheaf sections.
The residue is the genuine u=1-kernel contraction; only the uniform ordinary
Laurent normalization is supplied from the coefficient theory.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.GradedMilnorWittPathColumn
open CategoryTheory AlgebraicGeometry
open Verification.PathMilnorWittTriple Verification.PathMilnorWittWords
open Verification.PathMilnorWittWordFace
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (hs : Algebra.Smooth R S) (P : GradedMilnorWittLaurent.Standard R site N D K)
local notation "D₀" => D.symbols (CommRingCat.of S)
local notation "D₁" => D.symbols (CommRingCat.of (LaurentBasepoint.Laurent S))
local notation "f" => (LaurentBasepoint.coefficient R S).toRingHom
local notation "F" => GradedMilnorWittLaurent.coefficient R site N D S
local notation "r" => GradedMilnorWittLaurent.residue R site N D K S hs

include P in
theorem signed_column (w : ℕ) (xs ys : List (Sˣ × Bool)) (a : Sˣ) (l m t : Bool) :
    r (monomial D₁ ((selected xs).map (Units.map (f).toMonoidHom)) *
      word ((D₁).symbol (Units.map (f).toMonoidHom a))
        ((D₁).symbol ((-1:(LaurentBasepoint.Laurent S)ˣ)^w*LaurentPolynomialUniversal.parameterUnit S))
        ((D₁).symbol (Units.map (f).toMonoidHom a)) (l,m,t) *
      monomial D₁ ((selected ys).map (Units.map (f).toMonoidHom))) =
    (D₀).g^w * evaluate D₀ (xs.map Prod.fst ++ a::ys.map Prod.fst)
      (Verification.PathRhoWords.faceColumn (-Verification.PathCoefficientRing.g)
        Verification.PathCoefficientRing.rho (xs.map Prod.snd).length
        (xs.map Prod.snd ++ l::m::t::ys.map Prod.snd)) :=
  PathMilnorWittSignedWordFace.signed_column D₀ D₁ f F
    (GradedMilnorWittSheaf.compatible site N D
      (S:=CommRingCat.of S) (T:=CommRingCat.of (LaurentBasepoint.Laurent S)) f)
    (LaurentPolynomialUniversal.parameterUnit S) r
    (GradedMilnorWittLaurent.constant R site N D K S hs)
    (GradedMilnorWittLaurent.parameter R site N D K S hs P) w xs ys a l m t

include P in
theorem signed_column_right (w : ℕ) (xs ys : List (Sˣ × Bool)) (a : Sˣ) (l m t : Bool)
    (c : D.Total (CommRingCat.of S)) :
    r ((monomial D₁ ((selected xs).map (Units.map (f).toMonoidHom)) *
      word ((D₁).symbol (Units.map (f).toMonoidHom a))
        ((D₁).symbol ((-1:(LaurentBasepoint.Laurent S)ˣ)^w*LaurentPolynomialUniversal.parameterUnit S))
        ((D₁).symbol (Units.map (f).toMonoidHom a)) (l,m,t) *
      monomial D₁ ((selected ys).map (Units.map (f).toMonoidHom))) * F c) =
    ((D₀).g^w * evaluate D₀ (xs.map Prod.fst ++ a::ys.map Prod.fst)
      (Verification.PathRhoWords.faceColumn (-Verification.PathCoefficientRing.g)
        Verification.PathCoefficientRing.rho (xs.map Prod.snd).length
        (xs.map Prod.snd ++ l::m::t::ys.map Prod.snd))) * c := by
  rw [GradedMilnorWittLaurentWords.residue_coefficient_mul R S site N D K hs P,signed_column R S site N D K hs P]

#print axioms signed_column
#print axioms signed_column_right
end Verification.GradedMilnorWittPathColumn
