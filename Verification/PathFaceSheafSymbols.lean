/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFaceVertexTransport
import Verification.GradedMilnorWittPathColumn

/-!
# Path Face Sheaf Symbols

Actual sheaf-ring pullback on all signed path face units and ordered
coefficient words. Pullbacks are built from the genuine sheaf maps.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathFaceSheafSymbols
open CategoryTheory AlgebraicGeometry
open Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathSignedFaceUnits
open Verification.PathFaceVertexTransport Verification.PathMilnorWittWords
open Verification.PathMilnorWittWordFace Finset
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

def pullback : D.Total (CommRingCat.of Old) →+* D.Total (CommRingCat.of (LaurentBasepoint.Laurent New)) :=
  GradedMilnorWittSheaf.pullback site N D (S:=CommRingCat.of Old)
    (T:=CommRingCat.of (LaurentBasepoint.Laurent New)) (PathFaceVertexTransport.map R S hI a b j hj ha w).toRingHom

theorem remaining_symbol (p : Vertices n (insert j I)) :
    pullback R S hI a b j hj ha w site N D ((DO).symbol (signedCoordinate S hI a b (oldVertex j p)))=
      F ((DN).symbol (signedCoordinate S hJ a b p)) := by
  rw [pullback,GradedMilnorWittSheaf.pullback_symbol,remaining_unit]
  exact (GradedMilnorWittSheaf.pullback_symbol site N D
    (S:=CommRingCat.of New) (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
    (LaurentBasepoint.coefficient R New).toRingHom (signedCoordinate S hJ a b p)).symm

theorem normal_symbol : pullback R S hI a b j hj ha w site N D
    ((DO).symbol (signedCoordinate S hI a b (normalVertex j hj ha)))=
      (DL).symbol ((-1)^w*LaurentPolynomialUniversal.parameterUnit New) := by
  rw [pullback,GradedMilnorWittSheaf.pullback_symbol,normal_unit]

theorem remaining_monomial (xs : List (Vertices n (insert j I))) :
    pullback R S hI a b j hj ha w site N D
      (monomial DO (xs.map (fun p => signedCoordinate S hI a b (oldVertex j p))))=
      F (monomial DN (xs.map (signedCoordinate S hJ a b))) := by
  induction xs with
  | nil => simp only [List.map_nil,monomial,map_one]
  | cons p xs ih =>
    simp only [List.map_cons,monomial,map_mul,remaining_symbol,ih]

theorem remaining_word (xs : List (Vertices n (insert j I) × Bool)) :
    pullback R S hI a b j hj ha w site N D
      (monomial DO (selected (xs.map (fun x => (signedCoordinate S hI a b (oldVertex j x.1),x.2)))))=
      F (monomial DN (selected (xs.map (fun x => (signedCoordinate S hJ a b x.1,x.2))))) := by
  induction xs with
  | nil => simp only [List.map_nil,selected,monomial,map_one]
  | cons x xs ih =>
    rcases x with ⟨p,c⟩
    cases c <;> simp only [List.map_cons,selected,Bool.false_eq_true,↓reduceIte,monomial,map_mul,remaining_symbol,ih]

#print axioms pullback
#print axioms remaining_symbol
#print axioms normal_symbol
#print axioms remaining_monomial
#print axioms remaining_word
end Verification.PathFaceSheafSymbols
