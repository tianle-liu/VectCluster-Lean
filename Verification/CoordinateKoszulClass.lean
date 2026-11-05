/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SchemeGZeroInput
import Verification.StableFree

/-!
# Coordinate Koszul Class

Apply the uniform Koszul resolution theorem to a literal coordinate
closed immersion. The global cover, quotient identification and map
compatibility are constructed; only regularity on the principal chart
is left for the subsequent original-exchange-ring specialization.
-/
noncomputable section
namespace Verification.CoordinateKoszulClass
open CategoryTheory AlgebraicGeometry
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (I : Finset V)

def ordered : List I := by classical exact Finset.univ.toList
def equations : List A := (ordered V I).map (fun i => x i.val)

omit [Fintype V] [DecidableEq V] in
theorem mem_ordered (i : I) : i∈ordered V I := by classical simp [ordered]
omit [Fintype V] [DecidableEq V] in
theorem ordered_nodup : (ordered V I).Nodup := by classical exact Finset.nodup_toList _
omit [CommRing A] [Fintype V] [DecidableEq V] in
theorem length_equations : (equations A V x I).length=I.card := by
  classical
  simp [equations,ordered]

theorem ideal_eq : Ideal.ofList ((equations A V x I).map
    (algebraMap A (PrimeStratumPresentation.OpenRing x I)))=
      PrimeStratumPresentation.zeroIdeal x I := by
  apply congrArg Ideal.span
  ext a
  simp only [equations,List.map_map,PrimeStratumPresentation.zeroIdeal]
  change (a∈(ordered V I).map (fun i => algebraMap A (PrimeStratumPresentation.OpenRing x I) (x i.val))) ↔
    ∃ i : I,algebraMap A (PrimeStratumPresentation.OpenRing x I) (x i.val)=a
  simp only [List.mem_map,mem_ordered,true_and]

def quotientEquiv : PrimeStratumPresentation.ClosedRing x I ≃ₐ[PrimeStratumPresentation.OpenRing x I]
    (PrimeStratumPresentation.OpenRing x I ⧸ Ideal.ofList
      ((equations A V x I).map (algebraMap A (PrimeStratumPresentation.OpenRing x I)))) :=
  Ideal.quotientEquivAlgOfEq _ (ideal_eq A V x I).symm

def quotientIso : CoordinateClosedImmersion.source A V x I ≅
    Spec (CommRingCat.of (PrimeStratumPresentation.OpenRing x I ⧸ Ideal.ofList
      ((equations A V x I).map (algebraMap A (PrimeStratumPresentation.OpenRing x I))))) :=
  Scheme.Spec.mapIso (quotientEquiv A V x I).toRingEquiv.toCommRingCatIso.symm.op

theorem quotientIso_fac :
    (quotientIso A V x I).hom ≫ Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.ofList ((equations A V x I).map
        (algebraMap A (PrimeStratumPresentation.OpenRing x I))))).comp
          (algebraMap A (PrimeStratumPresentation.OpenRing x I)))) =
      CoordinateClosedImmersion.globalMap A V x I := by
  change Spec.map (CommRingCat.ofHom (quotientEquiv A V x I).symm.toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  congr 1

theorem cover : CoordinateClosedImmersion.ambient A V x I ≤
    PrimeSpectrum.basicOpen (∏ i∈Iᶜ,x i) ⊔
      ⨆ b : {b : A // b∈equations A V x I},PrimeSpectrum.basicOpen b.val := by
  have h := PrimeKoszulCover.cover x I
  apply le_trans h
  apply sup_le_sup
  · rfl
  · apply iSup_le
    intro i
    apply le_iSup_of_le ⟨x i.val,List.mem_map.mpr ⟨i,mem_ordered V I i,rfl⟩⟩
    rfl

variable {G : Scheme → Type*} [∀ X,AddCommGroup (G X)]
variable (T : SchemeGZeroInput.Theory G) (K : SchemeGZeroInput.Koszul T)
variable [IsNoetherianRing A]
variable (hreg : RingTheory.Sequence.IsWeaklyRegular (PrimeStratumPresentation.OpenRing x I)
  ((equations A V x I).map (algebraMap A (PrimeStratumPresentation.OpenRing x I))))

include K hreg in
theorem class_formula : T.push (CoordinateClosedImmersion.inclusion A V x I) inferInstance
    (T.unit (CoordinateClosedImmersion.source A V x I)) =
      ∑ p∈Finset.range (I.card+1),((-1)^p*I.card.choose p : ℤ) •
        T.unit (CoordinateClosedImmersion.ambient A V x I).toScheme := by
  have h := K.resolution_class A (CoordinateClosedImmersion.ambient A V x I)
    (∏ i∈Iᶜ,x i) (equations A V x I) hreg (cover A V x I)
    (CoordinateClosedImmersion.source A V x I) (CoordinateClosedImmersion.inclusion A V x I)
    inferInstance (quotientIso A V x I)
    ((CoordinateClosedImmersion.inclusion_fac A V x I).trans (quotientIso_fac A V x I).symm)
  simpa only [length_equations] using h

include K hreg in
theorem class_zero (hne : I.Nonempty) :
    T.push (CoordinateClosedImmersion.inclusion A V x I) inferInstance
      (T.unit (CoordinateClosedImmersion.source A V x I))=0 := by
  rw [class_formula A V x I T K hreg]
  exact StableFree.koszul_class_zero I.card (Finset.card_ne_zero.mpr hne) _

#print axioms ordered
#print axioms equations
#print axioms mem_ordered
#print axioms ordered_nodup
#print axioms length_equations
#print axioms ideal_eq
#print axioms quotientEquiv
#print axioms quotientIso
#print axioms quotientIso_fac
#print axioms cover
#print axioms class_formula
#print axioms class_zero
end Verification.CoordinateKoszulClass
