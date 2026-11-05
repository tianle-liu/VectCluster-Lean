/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.MilnorWittOneDimensional
import Verification.SheafGradedLaurentResidue
import Verification.LaurentPolynomialUniversal
import Verification.OriginalTorus
import Verification.TorusSmooth

/-!
# Witt Sheaf Sections Input

Uniform ordinary Witt references, with the actual coefficient sheaf and
its genuine u=1 contraction retained. A ring presheaf supplies Witt section
rings; the eta-periodic MW symbols determine one-dimensional forms.
The split-torus basis and Laurent normalization are stated for all smooth
coefficient algebras/finite tori, with no exchange matrix, stratum, or row.
-/
noncomputable section
namespace Verification.WittSheafSectionsInput
open CategoryTheory AlgebraicGeometry Opposite
open Verification.MilnorWittSymbolRelations Verification.MilnorWittOneDimensional
variable (R : Type) [CommRing R]
variable (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0})

abbrev RingSection (S : Type) [CommRing S] := W.obj (op (Spec (CommRingCat.of S)))

def pullback {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) :
    RingSection W S →+* RingSection W T :=
  (W.map (Spec.map (CommRingCat.ofHom f)).op).hom

structure Symbols where
  symbols : ∀ (S : Type) [CommRing S] [Algebra R S], Algebra.Smooth R S →
    MilnorWittSymbolRelations.Symbols S (RingSection W S)
  eta_unit : ∀ (S : Type) [CommRing S] [Algebra R S] (hs : Algebra.Smooth R S),
    IsUnit (symbols S hs).eta
  natural : ∀ (S T : Type) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hs : Algebra.Smooth R S) (ht : Algebra.Smooth R T) (f : S →ₐ[R] T),
    MilnorWittSymbolNaturality.Compatible (symbols S hs) (symbols T ht) f.toRingHom
      (pullback W f.toRingHom)

variable (D : Symbols R W)

def form (S : Type) [CommRing S] [Algebra R S] (hs : Algebra.Smooth R S) :
    Sˣ →* RingSection W S := oneDimHom (D.symbols S hs)

theorem form_square (S : Type) [CommRing S] [Algebra R S] (hs : Algebra.Smooth R S) (u : Sˣ) :
    form R W D S hs u * form R W D S hs u = 1 := oneDim_square _ u

theorem form_negative_one (S : Type) [CommRing S] [Algebra R S] (hs : Algebra.Smooth R S) :
    form R W D S hs (-1) = -1 := witt_negative _ (D.eta_unit S hs)

theorem form_natural (S T : Type) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hs : Algebra.Smooth R S) (ht : Algebra.Smooth R T) (f : S →ₐ[R] T) (u : Sˣ) :
    pullback W f.toRingHom (form R W D S hs u) =
      form R W D T ht (Units.map f.toRingHom.toMonoidHom u) :=
  map_oneDim (D.symbols S hs) (D.symbols T ht) f.toRingHom (pullback W f.toRingHom)
    (D.natural S T hs ht f) u

variable (site : GrothendieckTopology Scheme.{0})
variable (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))

structure Comparison where
  sections : ∀ (S : Type) [CommRing S] [Algebra R S], Algebra.Smooth R S → ∀ q : ℤ,
    RingSection W S ≃+ (N q).val.obj (op (Spec (CommRingCat.of S)))
  natural : ∀ (S T : Type) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hs : Algebra.Smooth R S) (ht : Algebra.Smooth R T) (f : S →ₐ[R] T) (q : ℤ)
    (a : RingSection W S),
    sections T ht q (pullback W f.toRingHom a) =
      (N q).val.map (Spec.map (CommRingCat.ofHom f.toRingHom)).op (sections S hs q a)

variable (E : Comparison R W site N)
variable (K : StandardThomContractionNormalization.Grading R site N)

structure LaurentNormalization : Prop where
  parameter : ∀ (S : Type) [CommRing S] [Algebra R S] (hs : Algebra.Smooth R S) (q : ℤ)
    (a : RingSection W S),
    letI := hs
    SheafGradedLaurentResidue.degreeResidue R S site N K hs q
      (E.sections (LaurentBasepoint.Laurent S) (ActualOldFiberSmooth.laurent_smooth R S) q
        (form R W D (LaurentBasepoint.Laurent S) (ActualOldFiberSmooth.laurent_smooth R S)
          (LaurentPolynomialUniversal.parameterUnit S) *
            pullback W (LaurentBasepoint.coefficient R S).toRingHom a)) =
      E.sections S hs (q-1) a

/-- The ordinary split-torus Witt basis, compatible with coefficients and
with the actual character units. This is uniform in every finite torus. -/
structure TorusBasis where
  equiv : ∀ (ι : Type) [Fintype ι],
    MonoidAlgebra (RingSection W R) (Multiplicative (ι → ZMod 2)) ≃+*
      RingSection W (OriginalTorus.Torus R ι)
  coefficient : ∀ (ι : Type) [Fintype ι] (a : RingSection W R),
    equiv ι (algebraMap (RingSection W R) _ a) =
      pullback W (algebraMap R (OriginalTorus.Torus R ι)) a
  character : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (i : ι),
    equiv ι (MonoidAlgebra.of (RingSection W R) _ (Multiplicative.ofAdd (Pi.single i 1))) =
      form R W D (OriginalTorus.Torus R ι) (TorusSmooth.torus_smooth R ι)
        ((MonoidAlgebra.of R (Multiplicative (ι →₀ ℤ))).toHomUnits
          (Multiplicative.ofAdd (Finsupp.single i 1)))

#print axioms RingSection
#print axioms pullback
#print axioms Symbols
#print axioms form
#print axioms form_square
#print axioms form_negative_one
#print axioms form_natural
#print axioms Comparison
#print axioms LaurentNormalization
#print axioms TorusBasis
end Verification.WittSheafSectionsInput
