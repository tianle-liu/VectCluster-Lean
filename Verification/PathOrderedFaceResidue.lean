/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOrderedFaceUnits
import Verification.PathMilnorWittListFace
import Verification.PathFaceSheafSymbols

/-!
# Path Ordered Face Residue

Every full ordered surviving-coordinate word has the literal rho face
column under the genuine sheaf Laurent residue. Both list order and the
normal sign come from the actual path geometry.
-/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1000000
namespace Verification.PathOrderedFaceResidue
open CategoryTheory AlgebraicGeometry Finset
open Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathSignedFaceUnits
open Verification.PathRepresentativeFaceList Verification.PathOrderedFaceUnits
open Verification.PathMilnorWittWordFace

theorem value_naturality {S T A B : Type*} [CommRing S] [CommRing T] [Ring A] [Ring B]
    (D₀ : MilnorWittSymbolRelations.Symbols S B) (D₁ : MilnorWittSymbolRelations.Symbols T A)
    (f : S →+* T) (F : B →+* A) (h : MilnorWittSymbolNaturality.Compatible D₀ D₁ f F)
    (xs : List Sˣ) (bs : List Bool) :
    F (wordValue D₀ xs bs)=wordValue D₁ (xs.map (Units.map f.toMonoidHom)) bs := by
  induction xs generalizing bs with
  | nil => simp only [wordValue,List.map_nil,map_one]
  | cons x xs ih =>
    cases bs with
    | nil => simp only [wordValue,List.map_cons,map_one]
    | cons b bs =>
      cases b <;> simp only [wordValue,List.map_cons,PathMilnorWittTriple.bit,Bool.false_eq_true,
        ↓reduceIte,map_mul,map_one,h.symbol,ih]

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (a b : S)
variable (j : ℕ) (hj : j∈Icc 1 n) (ha : Addable I j) (w : ℕ)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (hs : Algebra.Smooth R (Coefficients S (nextAdmissible hI j hj ha) a b))
variable (P : GradedMilnorWittLaurent.Standard R site N D K)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "Old" => Coefficients S hI a b
local notation "New" => Coefficients S (nextAdmissible hI j hj ha) a b
local notation "DO" => D.symbols (CommRingCat.of Old)
local notation "DN" => D.symbols (CommRingCat.of New)
local notation "DL" => D.symbols (CommRingCat.of (LaurentBasepoint.Laurent New))
local notation "F" => GradedMilnorWittLaurent.coefficient R site N D New
local notation "φ" => PathFaceSheafSymbols.pullback R S hI a b j hj ha w site N D
local notation "r" => GradedMilnorWittLaurent.residue R site N D K New hs

include P in
theorem full_word (bits : List Bool) (hb : bits.length=(available I (n+2)).card) :
    r (φ (wordValue DO (units S hI a b) bits))=
      (DN).g^w * evaluate DN (units S hJ a b)
        (PathRhoWords.faceColumn (-PathCoefficientRing.g) PathCoefficientRing.rho (faceIndex I j) bits) := by
  let xs := ((representatives n I).take (faceIndex I j)).map (unitAt S hJ a b)
  let ys := ((representatives n I).drop (faceIndex I j+3)).map (unitAt S hJ a b)
  have hv := faceIndex_valid hI j hj ha
  have hvb : faceIndex I j+3≤bits.length := by omega
  have hx : xs.length=(bits.take (faceIndex I j)).length := by
    simp only [xs,List.length_map,List.length_take,length_representatives,hb]
  have hy : ys.length=(bits.drop (faceIndex I j+3)).length := by
    simp only [ys,List.length_map,List.length_drop,length_representatives,hb]
  have hlen : (bits.take (faceIndex I j)).length=faceIndex I j := List.length_take_of_le (by omega)
  have he := split_three bits (faceIndex I j) hvb
  have hh := PathMilnorWittListFace.full_column DN DL (LaurentBasepoint.coefficient R New).toRingHom F
    (GradedMilnorWittSheaf.compatible site N D
      (S:=CommRingCat.of New) (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
      (LaurentBasepoint.coefficient R New).toRingHom)
    (LaurentPolynomialUniversal.parameterUnit New) r
    (GradedMilnorWittLaurent.constant R site N D K New hs)
    (GradedMilnorWittLaurent.parameter R site N D K New hs P) w
    xs ys (bits.take (faceIndex I j)) (bits.drop (faceIndex I j+3)) hx hy
    (unitAt S hJ a b (representative I (j-1))) bits[faceIndex I j] bits[faceIndex I j+1] bits[faceIndex I j+2]
  dsimp only [xs,ys] at hh
  have hc : (LaurentBasepoint.coefficient R New).toRingHom=algebraMap New (LaurentBasepoint.Laurent New) := rfl
  rw [hc] at hh
  rw [←source_units S hI a b R j hj ha w,←target_units S hI a b j hj ha,←he,hlen] at hh
  rw [value_naturality DO DL (PathFaceVertexTransport.map R S hI a b j hj ha w).toRingHom φ
    (GradedMilnorWittSheaf.compatible site N D
      (S:=CommRingCat.of Old) (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
      (PathFaceVertexTransport.map R S hI a b j hj ha w).toRingHom)]
  exact hh

#print axioms value_naturality
#print axioms full_word
end Verification.PathOrderedFaceResidue
