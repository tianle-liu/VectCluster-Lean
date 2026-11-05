/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostTorusVanishing
import Verification.SmithComponents
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Rost Finite Products

Positive-degree Rost acyclicity for the manuscript's actual tame
Smith strata, including nonconnected finite separable factors. Only
ordinary additivity over finite disjoint affine unions is supplied.
-/
noncomputable section
namespace Verification.RostFiniteProducts
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable (T : RostAffineInput.Theory)

structure Standard where
  product : ∀ (ι : Type) [Fintype ι] (R : ι→Type) [∀ i,CommRing (R i)] (s : ℤ) (q : ℕ),
    ((T.cycles (Spec (CommRingCat.of (∀ i,R i))) s).homology q ≃+
      ∀ i,(T.cycles (Spec (CommRingCat.of (R i))) s).homology q)

variable (F : Standard T)

include F in
theorem product_positive (ι : Type) [Fintype ι] (R : ι→Type) [∀ i,CommRing (R i)]
    (s : ℤ) (q : ℕ) (hz : ∀ i,IsZero ((T.cycles (Spec (CommRingCat.of (R i))) s).homology q)) :
    IsZero ((T.cycles (Spec (CommRingCat.of (∀ i,R i))) s).homology q) := by
  have hzero (i : ι) (a : (T.cycles (Spec (CommRingCat.of (R i))) s).homology q) : a=0 :=
    congrArg (fun f : (T.cycles (Spec (CommRingCat.of (R i))) s).homology q ⟶
      (T.cycles (Spec (CommRingCat.of (R i))) s).homology q => f a) ((hz i).eq_of_src (𝟙 _) 0)
  letI : Subsingleton ((T.cycles (Spec (CommRingCat.of (∀ i,R i))) s).homology q) :=
    ⟨fun a b => (F.product ι R s q).injective (by
      funext i
      exact (hzero i _).trans (hzero i _).symm)⟩
  exact AddCommGrp.isZero_of_subsingleton _

def torusCoordinates (k J : Type) [CommRing k] [Fintype J] :
    MonoidAlgebra k (Multiplicative (J→₀ℤ)) ≃ₐ[k]
      MonoidAlgebra k (Multiplicative (Fin (Fintype.card J)→₀ℤ)) :=
  MonoidAlgebra.domCongr k k
    (Finsupp.domLCongr (Fintype.equivFin J) : (J→₀ℤ) ≃ₗ[ℤ] (Fin (Fintype.card J)→₀ℤ)).toAddEquiv.toMultiplicative

theorem affine_torus_positive (k I J : Type) [Field k] [Fintype I] [Finite J]
    (s : ℤ) (q : ℕ) (hq : 0<q) :
    IsZero ((T.cycles (Spec (CommRingCat.of (MvPolynomial I
      (MonoidAlgebra k (Multiplicative (J→₀ℤ)))))) s).homology q) := by
  letI : Fintype J := Fintype.ofFinite J
  let e := MvPolynomial.mapAlgEquiv I (torusCoordinates k J)
  exact IsZero.of_iso (RostTorusVanishing.affine_torus_positive T k I (Fintype.card J) s q hq)
    (T.iso (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op) s q)

open Verification.GlobalSmithStratum Verification.PartialPowerProduct
open Verification.ActualStratum Verification.ExchangeCharacters Verification.DiagonalPowerFibers
variable {k I K τ P : Type} [Field k] [AddCommGroup P] [Fintype I] [Fintype K]

include F in
theorem smith_stratum_positive
    (j : τ→K) (B : (I⊕K)→(I⊕τ)→ℤ)
    (hB : ∀ a i : I,B (Sum.inl a) (Sum.inl i)=0)
    (f : P→ₗ[ℤ](K→₀ℤ)) (b : Basis I ℤ P)
    (hf : ∀ i,f (b i)=column Finset.univ (fun a => B (Sum.inr a) (Sum.inl i)) (fun v => Finsupp.single v 1))
    (hinj : Function.Injective f) {m : ℕ} (sm : Basis.SmithNormalForm (LinearMap.range f) K m)
    (he : ∀ i,IsUnit ((sm.a i).natAbs : k)) (s : ℤ) (q : ℕ) (hq : 0<q) :
    IsZero ((T.cycles (Spec (CommRingCat.of (GlobalZeroStratum k I K τ j B))) s).homology q) := by
  obtain ⟨J,hJ,L,hL,aL,e,_⟩ := SmithComponents.zero_stratum_separable_product j B hB f b hf hinj sm he
  letI := hJ
  letI := hL
  letI := aL
  letI : Fintype J := Fintype.ofFinite J
  have h := product_positive T F J (fun i => MvPolynomial I (Laurent (L i) (FreeIndex (smithEmbedding f sm)))) s q
    (fun i => affine_torus_positive T (L i) I (FreeIndex (smithEmbedding f sm)) s q hq)
  exact IsZero.of_iso h (T.iso (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op) s q)

#print axioms Standard
#print axioms product_positive
#print axioms torusCoordinates
#print axioms affine_torus_positive
#print axioms smith_stratum_positive
end Verification.RostFiniteProducts
