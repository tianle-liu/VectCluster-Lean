/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFaceSheafSymbols
import Verification.GradedMilnorWittScalarNaturality

/-!
# Path Face Actual Word Residue

The canonical path face on actual sheaf sections has the full rho word
column, with its literal normal sign and arbitrary scalar coefficients.
-/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1000000
namespace Verification.PathFaceActualWordResidue
open CategoryTheory AlgebraicGeometry
open Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathSignedFaceUnits
open Verification.PathFaceVertexTransport Verification.PathMilnorWittTriple Verification.PathMilnorWittWords
open Verification.PathMilnorWittWordFace Finset
theorem ringHom_word {A B : Type*} [Ring A] [Ring B] (f : A →+* B) (x y z : A)
    (u : Verification.PathRhoFaces.Triple) : f (word x y z u)=word (f x) (f y) (f z) u := by
  rcases u with ⟨l,m,t⟩
  cases l <;> cases m <;> cases t <;> simp only [word,bit,Bool.false_eq_true,↓reduceIte,map_mul,map_one]

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (a b : S)
variable (j : ℕ) (hj : j∈Icc 1 n) (ha : Addable I j) (w : ℕ)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "Old" => Coefficients S hI a b
local notation "New" => Coefficients S (nextAdmissible hI j hj ha) a b
local notation "DO" => D.symbols (CommRingCat.of Old)
local notation "DN" => D.symbols (CommRingCat.of New)
local notation "DL" => D.symbols (CommRingCat.of (LaurentBasepoint.Laurent New))
local notation "F" => GradedMilnorWittLaurent.coefficient R site N D New
local notation "φ" => PathFaceSheafSymbols.pullback R S hI a b j hj ha w site N D
local notation "left" => leftVertex (nextAdmissible hI j hj ha) ⟨j,mem_insert_self j I⟩
local notation "right" => rightVertex (nextAdmissible hI j hj ha) ⟨j,mem_insert_self j I⟩

def targetPairs (xs : List (Vertices n (insert j I) × Bool)) : List (Newˣ × Bool) :=
  xs.map (fun x => (signedCoordinate S hJ a b x.1,x.2))

def sourceWord (xs ys : List (Vertices n (insert j I) × Bool)) (l m t : Bool) : D.Total (CommRingCat.of Old) :=
  monomial DO (selected (xs.map (fun x => (signedCoordinate S hI a b (oldVertex j x.1),x.2)))) *
    word ((DO).symbol (signedCoordinate S hI a b (oldVertex j left)))
      ((DO).symbol (signedCoordinate S hI a b (normalVertex j hj ha)))
      ((DO).symbol (signedCoordinate S hI a b (oldVertex j right))) (l,m,t) *
    monomial DO (selected (ys.map (fun x => (signedCoordinate S hI a b (oldVertex j x.1),x.2))))

theorem pullback_word (xs ys : List (Vertices n (insert j I) × Bool)) (l m t : Bool) :
    φ (sourceWord S hI a b j hj ha site N D xs ys l m t)=
      F (monomial DN (selected (targetPairs S hI a b j hj ha xs))) *
        word (F ((DN).symbol (signedCoordinate S hJ a b left)))
          ((DL).symbol ((-1)^w*LaurentPolynomialUniversal.parameterUnit New))
          (F ((DN).symbol (signedCoordinate S hJ a b left))) (l,m,t) *
      F (monomial DN (selected (targetPairs S hI a b j hj ha ys))) := by
  unfold sourceWord
  rw [map_mul,map_mul,PathFaceSheafSymbols.remaining_word R S hI a b j hj ha w site N D xs,
    PathFaceSheafSymbols.remaining_word R S hI a b j hj ha w site N D ys]
  have hl : φ ((DO).symbol (signedCoordinate S hI a b (oldVertex j left)))=
      F ((DN).symbol (signedCoordinate S hJ a b left)) :=
    PathFaceSheafSymbols.remaining_symbol R S hI a b j hj ha w site N D left
  have hr : φ ((DO).symbol (signedCoordinate S hI a b (oldVertex j right)))=
      F ((DN).symbol (signedCoordinate S hJ a b right)) :=
    PathFaceSheafSymbols.remaining_symbol R S hI a b j hj ha w site N D right
  rw [PathFaceVertexTransport.neighbors S hI a b j hj ha] at hr
  have hn : φ ((DO).symbol (signedCoordinate S hI a b (normalVertex j hj ha)))=
      (DL).symbol ((-1)^w*LaurentPolynomialUniversal.parameterUnit New) :=
    PathFaceSheafSymbols.normal_symbol R S hI a b j hj ha w site N D
  rw [ringHom_word,hl,hr,hn]
  rfl

variable (K : StandardThomContractionNormalization.Grading R site N)
variable (hs : Algebra.Smooth R (Coefficients S (nextAdmissible hI j hj ha) a b))
variable (P : GradedMilnorWittLaurent.Standard R site N D K)
local notation "r" => GradedMilnorWittLaurent.residue R site N D K New hs

include P in
theorem residue_word (xs ys : List (Vertices n (insert j I) × Bool)) (l m t : Bool) :
    r (φ (sourceWord S hI a b j hj ha site N D xs ys l m t))=
      (DN).g^w * evaluate DN
        ((targetPairs S hI a b j hj ha xs).map Prod.fst ++
          signedCoordinate S hJ a b left :: (targetPairs S hI a b j hj ha ys).map Prod.fst)
        (Verification.PathRhoWords.faceColumn (-Verification.PathCoefficientRing.g)
          Verification.PathCoefficientRing.rho ((targetPairs S hI a b j hj ha xs).map Prod.snd).length
          ((targetPairs S hI a b j hj ha xs).map Prod.snd ++
            l::m::t::(targetPairs S hI a b j hj ha ys).map Prod.snd)) := by
  rw [pullback_word]
  have h := GradedMilnorWittSheaf.compatible site N D
    (S:=CommRingCat.of New) (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
    (LaurentBasepoint.coefficient R New).toRingHom
  have hh := GradedMilnorWittPathColumn.signed_column R New site N D K hs P w
    (targetPairs S hI a b j hj ha xs) (targetPairs S hI a b j hj ha ys)
    (signedCoordinate S hJ a b left) l m t
  rw [PathMilnorWittWords.pullback DN DL (LaurentBasepoint.coefficient R New).toRingHom F h,
    PathMilnorWittWords.pullback DN DL (LaurentBasepoint.coefficient R New).toRingHom F h,
    ← h.symbol] at hh
  exact hh


include P in
theorem residue_word_scalar (xs ys : List (Vertices n (insert j I) × Bool)) (l m t : Bool)
    (c : D.Total (CommRingCat.of R)) :
    r (φ (sourceWord S hI a b j hj ha site N D xs ys l m t *
      GradedMilnorWittScalarNaturality.scalar R Old site N D c))=
      r (φ (sourceWord S hI a b j hj ha site N D xs ys l m t)) *
        GradedMilnorWittScalarNaturality.scalar R New site N D c := by
  rw [map_mul]
  have ho := GradedMilnorWittScalarNaturality.naturality R Old (LaurentBasepoint.Laurent New) site N D
    (PathFaceVertexTransport.map R S hI a b j hj ha w) c
  change φ (GradedMilnorWittScalarNaturality.scalar R Old site N D c)=_ at ho
  rw [ho]
  have hn := GradedMilnorWittScalarNaturality.naturality R New (LaurentBasepoint.Laurent New) site N D
    (LaurentBasepoint.coefficient R New) c
  change F (GradedMilnorWittScalarNaturality.scalar R New site N D c)=_ at hn
  rw [← hn]
  exact GradedMilnorWittLaurentWords.residue_coefficient_mul R New site N D K hs P _ _

#print axioms ringHom_word
#print axioms targetPairs
#print axioms sourceWord
#print axioms pullback_word
#print axioms residue_word
#print axioms residue_word_scalar
end Verification.PathFaceActualWordResidue
