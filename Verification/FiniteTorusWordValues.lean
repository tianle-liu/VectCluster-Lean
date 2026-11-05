/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteTorusWordBasis
import Verification.OrderedBinaryWords

/-!
# Finite Torus Word Values

The constructed torus coordinates are precisely the ordered symbol
words multiplied on the right by actual base coefficient sections.
-/
noncomputable section
namespace Verification.FiniteTorusWordValues
open CategoryTheory AlgebraicGeometry
open Verification.OriginalTorus Verification.BinaryWordCoordinates
variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
local notation "C" => D.Total (CommRingCat.of R)
local notation "𝕋" n => CommRingCat.of (Torus R (Fin n))

def scalar (n : ℕ) : C →+* D.Total (𝕋 n) :=
  GradedMilnorWittSheaf.pullback site N D (S := CommRingCat.of R) (T := 𝕋 n)
    (algebraMap R (Torus R (Fin n)))

def symbol (n : ℕ) (i : Fin n) : D.Total (𝕋 n) :=
  (D.symbols (𝕋 n)).symbol (FinsuppTorusUniversal.unit R (Fin n) i)

def word (n : ℕ) (i : Index n) : D.Total (𝕋 n) :=
  OrderedBinaryWords.word n (symbol R site N D n) i

theorem coefficient_scalar (n : ℕ) (a : C) :
    FiniteTorusSectionSplit.coefficient R site N D n (scalar R site N D n a)=
      scalar R site N D (n+1) a := by
  have h : (FiniteTorusSectionSplit.coefficient R site N D n).comp (scalar R site N D n)=
      scalar R site N D (n+1) := by
    unfold FiniteTorusSectionSplit.coefficient scalar
    rw [← GradedMilnorWittSheaf.pullback_comp]
    congr 1
    exact (FiniteTorusLaurent.coefficient R n).comp_algebraMap
  exact RingHom.congr_fun h a

theorem coefficient_symbol (n : ℕ) (i : Fin n) :
    FiniteTorusSectionSplit.coefficient R site N D n (symbol R site N D n i)=
      symbol R site N D (n+1) i.succ := by
  unfold FiniteTorusSectionSplit.coefficient symbol
  rw [GradedMilnorWittSheaf.pullback_symbol]
  congr 1
  apply Units.ext
  exact FiniteTorusLaurent.coefficient_coordinate R n i

theorem coefficient_word (n : ℕ) (i : Index n) :
    FiniteTorusSectionSplit.coefficient R site N D n (word R site N D n i)=
      OrderedBinaryWords.word n (fun k => symbol R site N D (n+1) k.succ) i := by
  calc
    _=OrderedBinaryWords.word n
        (fun k => FiniteTorusSectionSplit.coefficient R site N D n (symbol R site N D n k)) i :=
      OrderedBinaryWords.map_word (FiniteTorusSectionSplit.coefficient R site N D n).toMonoidHom n _ i
    _=_ := by
      congr 1
      funext k
      exact coefficient_symbol R site N D n k

theorem value_word (n : ℕ) (i : Index n) (a : C) :
    FiniteTorusWordBasis.value R site N D n i a=word R site N D n i*scalar R site N D n a := by
  induction n with
  | zero =>
    change FiniteTorusSectionSplit.zeroEquiv R site N D a=1*scalar R site N D 0 a
    rw [one_mul]
    rfl
  | succ n ih =>
    rcases i with ⟨b,i⟩
    cases b
    · change FiniteTorusSectionSplit.coefficient R site N D n
        (FiniteTorusWordBasis.value R site N D n i a)=_
      rw [ih,map_mul,coefficient_word,coefficient_scalar]
      rfl
    · change FiniteTorusSectionSplit.firstSymbol R site N D n*
        FiniteTorusSectionSplit.coefficient R site N D n
          (FiniteTorusWordBasis.value R site N D n i a)=_
      rw [ih,map_mul,coefficient_word,coefficient_scalar,← mul_assoc]
      rfl

variable (K : StandardThomContractionNormalization.Grading R site N)
variable (P : GradedMilnorWittLaurent.Standard R site N D K)
include P

theorem basis_word (n : ℕ) (i : Index n) (a : C) :
    FiniteTorusWordBasis.basis R site N D K n (Pi.single i a)=
      word R site N D n i*scalar R site N D n a := by
  rw [FiniteTorusWordBasis.basis_single R site N D K P,value_word]

theorem basis_expansion (n : ℕ) (a : Index n → C) :
    FiniteTorusWordBasis.basis R site N D K n a=
      ∑ i,word R site N D n i*scalar R site N D n (a i) := by
  rw [FiniteTorusWordBasis.basis_expansion R site N D K P]
  apply Finset.sum_congr rfl
  intro i _
  exact value_word R site N D n i (a i)

#print axioms scalar
#print axioms symbol
#print axioms word
#print axioms coefficient_scalar
#print axioms coefficient_symbol
#print axioms coefficient_word
#print axioms value_word
#print axioms basis_word
#print axioms basis_expansion
end Verification.FiniteTorusWordValues
