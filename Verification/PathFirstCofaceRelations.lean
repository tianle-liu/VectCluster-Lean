/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFirstCofaces

/-!
# Path First Coface Relations

Every local transpose column at arbitrary position is a unit multiple
of the original kill or g-slide relation, before endpoint-word deletion.
-/

namespace Verification.PathFirstCofaceRelations

open Classical Verification.PathRhoWords Verification.PathRhoFaces Verification.PathRhoSeparated
  Verification.PathFirstCofaces

variable {R : Type*} [CommRing R]

noncomputable def prefixWords (pre : List Bool) : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R) :=
  Finsupp.lmapDomain R R (fun w => pre++w)

theorem prefixWords_single (pre w : List Bool) (r : R) :
    prefixWords pre (Finsupp.single w r)=Finsupp.single (pre++w) r := by
  simp only [prefixWords,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]

theorem prefixWords_nil : prefixWords (R := R) []=LinearMap.id := by
  apply Finsupp.lhom_ext
  intro w r
  rw [prefixWords_single]
  rfl

theorem prefixWords_cons (a : Bool) (pre : List Bool) :
    prefixWords (R := R) (a::pre)=(prepend a).comp (prefixWords pre) := by
  apply Finsupp.lhom_ext
  intro w r
  simp only [prefixWords_single,LinearMap.comp_apply,prepend_single,List.cons_append]

def prefixFactor (ε : R) : List Bool → R
  | [] => 1
  | a::pre => phase ε a*prefixFactor ε pre

theorem prefixFactor_squared (ε : R) (hε : ε*ε=1) (pre : List Bool) :
    prefixFactor ε pre*prefixFactor ε pre=1 := by
  induction pre with
  | nil => simp [prefixFactor]
  | cons a pre ih =>
    calc
      _=(phase ε a*phase ε a)*(prefixFactor ε pre*prefixFactor ε pre) := by rw [prefixFactor]; ring
      _=1 := by rw [phase_squared ε hε,ih,mul_one]

theorem coface_prefix (ε ρ : R) (pre v : List Bool) :
    cofaceColumn ε ρ pre.length (pre++v)=
      prefixFactor ε pre • prefixWords pre (cofaceColumn ε ρ 0 v) := by
  induction pre with
  | nil => simp only [List.length_nil,List.nil_append,prefixFactor,prefixWords_nil,LinearMap.id_apply,one_smul]
  | cons a pre ih =>
    simp only [List.length_cons,List.cons_append,cofaceColumn,ih,map_smul,
      prefixFactor,prefixWords_cons,LinearMap.comp_apply,smul_smul]

theorem kill_column (ε : R) (pre tail : List Bool) :
    cofaceColumn ε 0 pre.length (pre++false::tail)=
      prefixFactor ε pre • Finsupp.single (pre++false::true::false::tail) 1 := by
  rw [coface_prefix,coface_head_kill,prefixWords_single]

theorem slide_column (g : R) (hg : g*g=1) (pre tail : List Bool) :
    cofaceColumn (-g) 0 pre.length (pre++true::tail)=
      (prefixFactor (-g) pre*(-g)) •
        (Finsupp.single (pre++true::true::false::tail) 1-
          g • Finsupp.single (pre++false::true::true::tail) 1) := by
  rw [coface_prefix,coface_head_slide,map_add,map_smul,prefixWords_single,prefixWords_single]
  rw [smul_add,smul_sub,smul_smul,smul_smul]
  have he : (prefixFactor (-g) pre*(-g))*g= -prefixFactor (-g) pre := by
    rw [mul_assoc,neg_mul,hg,mul_neg,mul_one]
  rw [he,neg_smul,sub_neg_eq_add]

theorem relation_factor_squared (g : R) (hg : g*g=1) (pre : List Bool) :
    (prefixFactor (-g) pre*(-g))*(prefixFactor (-g) pre*(-g))=1 := by
  have hε : (-g)*(-g)=1 := by simpa only [neg_mul_neg] using hg
  calc
    _=(prefixFactor (-g) pre*prefixFactor (-g) pre)*((-g)*(-g)) := by ring
    _=1 := by rw [prefixFactor_squared (-g) hε,hε,mul_one]

#print axioms prefixWords
#print axioms prefixWords_single
#print axioms prefixWords_nil
#print axioms prefixWords_cons
#print axioms prefixFactor
#print axioms prefixFactor_squared
#print axioms coface_prefix
#print axioms kill_column
#print axioms slide_column
#print axioms relation_factor_squared

end Verification.PathFirstCofaceRelations
