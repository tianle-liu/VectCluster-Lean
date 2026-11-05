/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ModuleGrothendieck
import Verification.KoszulResolution
import Verification.CoordinateClosedLayer
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Scheme G Zero Input

Uniform reference interfaces for ordinary coherent G-theory. The
affine comparison is with the already defined Grothendieck group of finite
modules and actual short exact sequences. These interfaces contain no
exchange matrix, filtration, rank-isomorphism conclusion, or stable
freeness assertion. Localization and the finite free Koszul Euler formula
are kept separate from the geometry that permits their application.
-/
noncomputable section
namespace Verification.SchemeGZeroInput
open CategoryTheory AlgebraicGeometry
variable (G : Scheme → Type*) [∀ X,AddCommGroup (G X)]

structure Theory where
  unit : ∀ X,G X
  restrict : ∀ {U X : Scheme} (j : U⟶X), IsOpenImmersion j → (G X →+ G U)
  restrict_comp : ∀ {U X Y : Scheme} (i : U⟶X) (j : X⟶Y)
    (hi : IsOpenImmersion i) (hj : IsOpenImmersion j),
    restrict (i≫j) (by letI:=hi; letI:=hj; infer_instance) =
      (restrict i hi).comp (restrict j hj)
  restrict_id : ∀ X,restrict (𝟙 X) inferInstance = AddMonoidHom.id (G X)
  restrict_unit : ∀ {U X : Scheme} (j : U⟶X) (hj : IsOpenImmersion j),
    restrict j hj (unit X)=unit U
  push : ∀ {Z X : Scheme} (i : Z⟶X), IsClosedImmersion i → (G Z →+ G X)
  affine : ∀ (A : Type) [CommRing A] [IsNoetherianRing A],
    G (Spec (CommRingCat.of A)) ≃+ ModuleGrothendieck.Group A
  affine_unit : ∀ (A : Type) [CommRing A] [IsNoetherianRing A],
    affine A (unit (Spec (CommRingCat.of A)))=
      ModuleGrothendieck.classOf A (ModuleGrothendieck.of A A)

variable {G} (T : Theory G)

/-- The ordinary localization theorem, stated for an arbitrary finite
disjoint closed family whose union is the complement of an open. -/
structure Localization where
  surjective : ∀ {U X : Scheme} [IsNoetherian X] (j : U⟶X) (hj : IsOpenImmersion j),
    Function.Surjective (T.restrict j hj)
  kernel : ∀ {U X : Scheme} [IsNoetherian X] (j : U⟶X) (hj : IsOpenImmersion j)
    (ι : Type) [Fintype ι] (Z : ι→Scheme) (i : ∀ a,Z a⟶X)
    (hi : ∀ a,IsClosedImmersion (i a))
    (_hd : Pairwise (fun a b => Disjoint (Set.range (i a).base) (Set.range (i b).base)))
    (_hc : (⋃ a,Set.range (i a).base)=(Set.range j.base)ᶜ)
    (z : G X), T.restrict j hj z=0 →
      ∃ b : ∀ a,G (Z a),z=∑ a,T.push (i a) (hi a) (b a)

/-- A uniformly stated Koszul theorem on a noetherian affine open. The
listed global functions are regular on one principal chart, which together
with their unit loci covers the ambient open. This is precisely the usual
local exactness criterion for their finite free Koszul resolution; the
compatible quotient presentation fixes the pushed-forward structure sheaf.
The statement is independent of all cluster coordinates. -/
structure Koszul where
  resolution_class : ∀ (A : Type) [CommRing A] [IsNoetherianRing A]
    (U : (Spec (CommRingCat.of A)).Opens) (a : A) (l : List A)
    (_hreg : RingTheory.Sequence.IsWeaklyRegular (Localization.Away a)
      (l.map (algebraMap A (Localization.Away a))))
    (_hcover : U ≤ PrimeSpectrum.basicOpen a ⊔
      ⨆ b : {b : A // b∈l},PrimeSpectrum.basicOpen b.val)
    (Z : Scheme) (i : Z⟶U.toScheme) (hi : IsClosedImmersion i)
    (e : Z ≅ Spec (CommRingCat.of
      (Localization.Away a ⧸ Ideal.ofList (l.map (algebraMap A (Localization.Away a))))))
    (_he : i≫U.ι=e.hom≫Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.ofList (l.map (algebraMap A (Localization.Away a))))).comp
        (algebraMap A (Localization.Away a))))),
    T.push i hi (T.unit Z)=∑ p∈Finset.range (l.length+1),
      ((-1)^p*l.length.choose p : ℤ) • T.unit U.toScheme

/-- Homotopy invariance and the Laurent-polynomial fundamental theorem
give the structure-sheaf generator on affine space times a split torus. -/
structure SplitAffineTorus where
  generated : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (t : ℕ),
    Function.Surjective (fun n : ℤ => n • T.unit (Spec (CommRingCat.of
      (MvPolynomial ι (MonoidAlgebra k (Multiplicative (Fin t →₀ ℤ)))))))
  infinite_order : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (t : ℕ),
    Function.Injective (fun n : ℤ => n • T.unit (Spec (CommRingCat.of
      (MvPolynomial ι (MonoidAlgebra k (Multiplicative (Fin t →₀ ℤ)))))))

#print axioms Theory
#print axioms Localization
#print axioms Koszul
#print axioms SplitAffineTorus
end Verification.SchemeGZeroInput
