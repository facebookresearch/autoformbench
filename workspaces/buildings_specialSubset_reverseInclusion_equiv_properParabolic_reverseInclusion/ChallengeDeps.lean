/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option warningAsError false


























universe u v

namespace Autoform_Buildings_and_Classical_Groups_buildings_specialSubset_reverseInclusion_equiv_properParabolic_reverseInclusion




def setMul {G : Type u} [Mul G] (A B : Set G) : Set G :=
  {g : G | ∃ a : G, a ∈ A ∧ ∃ b : G, b ∈ B ∧ a * b = g}


def leftTranslateSet {G : Type u} [Mul G] (g : G) (A : Set G) : Set G :=
  {x : G | ∃ a : G, a ∈ A ∧ g * a = x}


def leftCoset {G : Type u} [Mul G] (g : G) (A : Set G) : Set G :=
  leftTranslateSet g A


def conjugateSet {G : Type u} [Group G] (g : G) (A : Set G) : Set G :=
  {x : G | ∃ a : G, a ∈ A ∧ g * a * g⁻¹ = x}



def conjugateSubgroup {G : Type u} [Group G] (g : G) (P : Subgroup G) : Subgroup G where
  carrier := conjugateSet g (P : Set G)
  one_mem' := by
    refine ⟨1, P.one_mem, ?_⟩
    group
  mul_mem' := by
    intro x y hx hy
    rcases hx with ⟨p, hp, rfl⟩
    rcases hy with ⟨q, hq, rfl⟩
    refine ⟨p * q, P.mul_mem hp hq, ?_⟩
    group
  inv_mem' := by
    intro x hx
    rcases hx with ⟨p, hp, rfl⟩
    refine ⟨p⁻¹, P.inv_mem hp, ?_⟩
    group


theorem conjugateSubgroup_ne_top {G : Type u} [Group G] (g : G) {P : Subgroup G}
    (hP : P ≠ ⊤) : conjugateSubgroup g P ≠ ⊤ := by
  intro htop
  apply hP
  apply SetLike.ext
  intro x
  constructor
  · intro _
    trivial
  · intro _
    have hxconj : g * x * g⁻¹ ∈ (conjugateSubgroup g P : Set G) := by
      rw [htop]
      trivial
    rcases hxconj with ⟨p, hp, hp_eq⟩
    have hpx : p = x := by
      calc
        p = g⁻¹ * (g * p * g⁻¹) * g := by group
        _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hp_eq]
        _ = x := by group
    simpa [hpx] using hp








def titsSubgroup {G : Type u} [Group G] (B N : Subgroup G) : Subgroup N :=
  Subgroup.comap N.subtype B





def bruhatCellOf {G : Type u} [Group G] (B : Subgroup G) (N : Subgroup G)
    (T : Subgroup N) [T.Normal] (w : N ⧸ T) : Set G :=
  {g : G |
    ∃ n : N,
      QuotientGroup.mk' T n = w ∧
        ∃ b₁ : G, b₁ ∈ B ∧ ∃ b₂ : G, b₂ ∈ B ∧ b₁ * (n : G) * b₂ = g}



def conjugateBOf {G : Type u} [Group G] (B : Subgroup G) (N : Subgroup G)
    (T : Subgroup N) [T.Normal] (w : N ⧸ T) : Set G :=
  {g : G |
    ∃ n : N,
      QuotientGroup.mk' T n = w ∧ g ∈ conjugateSet (n : G) (B : Set G)}



def specialSubgroupOf {ι : Type v} {M : CoxeterMatrix ι}
    {W : Type u} [Group W] (cs : CoxeterSystem M W) (I : Set ι) : Subgroup W :=
  Subgroup.closure (cs.simple '' I)


def standardParabolicSetOf {G : Type u} [Group G] {ι : Type v}
    {M : CoxeterMatrix ι} (B : Subgroup G) (N : Subgroup G) (T : Subgroup N)
    [T.Normal] (cs : CoxeterSystem M (N ⧸ T)) (I : Set ι) : Set G :=
  {g : G | ∃ w : N ⧸ T, w ∈ specialSubgroupOf cs I ∧ g ∈ bruhatCellOf B N T w}









structure StrictBNPair (G : Type u) [Group G] (ι : Type v) (M : CoxeterMatrix ι) where
  B : Subgroup G
  N : Subgroup G
  [normal_T : (titsSubgroup B N).Normal]
  coxeter : CoxeterSystem M (N ⧸ titsSubgroup B N)
  generate_BN : Subgroup.closure ((B : Set G) ∪ (N : Set G)) = ⊤
  bruhat_decomposition :
    ∀ g : G, ∃! w : N ⧸ titsSubgroup B N, g ∈ bruhatCellOf B N (titsSubgroup B N) w
  standardParabolic_isSubgroup :
    ∀ I : Set ι,
      ∃ P : Subgroup G,
        (P : Set G) = standardParabolicSetOf B N (titsSubgroup B N) coxeter I
  cell_mul_right_simple_of_length_gt :
    ∀ (w : N ⧸ titsSubgroup B N) (i : ι),
      coxeter.length (w * coxeter.simple i) > coxeter.length w →
        setMul (bruhatCellOf B N (titsSubgroup B N) w)
            (bruhatCellOf B N (titsSubgroup B N) (coxeter.simple i)) =
          bruhatCellOf B N (titsSubgroup B N) (w * coxeter.simple i)
  cell_mul_right_simple_of_length_lt :
    ∀ (w : N ⧸ titsSubgroup B N) (i : ι),
      coxeter.length (w * coxeter.simple i) < coxeter.length w →
        setMul (bruhatCellOf B N (titsSubgroup B N) w)
            (bruhatCellOf B N (titsSubgroup B N) (coxeter.simple i)) =
          bruhatCellOf B N (titsSubgroup B N) (w * coxeter.simple i) ∪
            bruhatCellOf B N (titsSubgroup B N) w
  simple_conjugate_not_subset_B :
    ∀ i : ι, ¬ (conjugateBOf B N (titsSubgroup B N) (coxeter.simple i) ⊆ (B : Set G))

attribute [instance] StrictBNPair.normal_T

variable {G : Type u} [Group G] {ι : Type v} {M : CoxeterMatrix ι}




def IsSpecialSubgroup (bn : StrictBNPair G ι M) (P : Subgroup G) : Prop :=
  P ≠ ⊤ ∧ bn.B ≤ P



def IsProperParabolicSubgroup (bn : StrictBNPair G ι M) (Q : Subgroup G) : Prop :=
  Q ≠ ⊤ ∧ ∃ g : G, conjugateSet g (bn.B : Set G) ⊆ (Q : Set G)



structure SpecialSubset (bn : StrictBNPair G ι M) where
  carrier : Set G
  exists_special_coset :
    ∃ g : G, ∃ P : Subgroup G, IsSpecialSubgroup bn P ∧ carrier = leftCoset g (P : Set G)

variable {bn : StrictBNPair G ι M}


def specialSubsetReverseLe (Y Z : SpecialSubset bn) : Prop :=
  Z.carrier ⊆ Y.carrier


def specialSubsetOf (bn : StrictBNPair G ι M) (g : G) (P : Subgroup G)
    (hP : IsSpecialSubgroup bn P) : SpecialSubset bn :=
  ⟨leftCoset g (P : Set G), ⟨g, P, hP, rfl⟩⟩


def specialSubsetLeftTranslate (bn : StrictBNPair G ι M) (a : G)
    (Y : SpecialSubset bn) : SpecialSubset bn where
  carrier := leftTranslateSet a Y.carrier
  exists_special_coset := by
    rcases Y.exists_special_coset with ⟨g, P, hP, hY⟩
    refine ⟨a * g, P, hP, ?_⟩
    rw [hY]
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      rcases hy with ⟨p, hp, hyp⟩
      refine ⟨p, hp, ?_⟩
      rw [← hxy, ← hyp]
      group
    · intro hx
      rcases hx with ⟨p, hp, hpx⟩
      refine ⟨g * p, ⟨p, hp, rfl⟩, ?_⟩
      rw [← hpx]
      group



structure ProperParabolicSubset (bn : StrictBNPair G ι M) where
  toSubgroup : Subgroup G
  is_proper_parabolic : IsProperParabolicSubgroup bn toSubgroup


def carrier (X : ProperParabolicSubset bn) : Set G :=
  (X.toSubgroup : Set G)


def properParabolicSubsetReverseLe (X Y : ProperParabolicSubset bn) : Prop :=
  (carrier Y) ⊆ (carrier X)


def properParabolicConjugate (bn : StrictBNPair G ι M) (a : G)
    (X : ProperParabolicSubset bn) : ProperParabolicSubset bn where
  toSubgroup := conjugateSubgroup a X.toSubgroup
  is_proper_parabolic := by
    rcases X.is_proper_parabolic with ⟨hproper, hcontains⟩
    refine ⟨conjugateSubgroup_ne_top a hproper, ?_⟩
    rcases hcontains with ⟨g, hg⟩
    refine ⟨a * g, ?_⟩
    intro x hx
    rcases hx with ⟨b, hb, rfl⟩
    refine ⟨g * b * g⁻¹, hg ?_, ?_⟩
    · exact ⟨b, hb, rfl⟩
    · group



end Autoform_Buildings_and_Classical_Groups_buildings_specialSubset_reverseInclusion_equiv_properParabolic_reverseInclusion
