/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

















universe u v

namespace Autoform_Buildings_and_Classical_Groups_buildings_closure_bruhatCell_contains_reduced_simples_and_eq_closure_B_union_conjugate


def setMul {G : Type u} [Mul G] (A B : Set G) : Set G :=
  {g : G | ∃ a : G, a ∈ A ∧ ∃ b : G, b ∈ B ∧ a * b = g}


def conjugateSet {G : Type u} [Group G] (a : G) (A : Set G) : Set G :=
  {g : G | ∃ x : G, x ∈ A ∧ a * x * a⁻¹ = g}





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



def conjugateBByInverseOf {G : Type u} [Group G] (B : Subgroup G) (N : Subgroup G)
    (T : Subgroup N) [T.Normal] (w : N ⧸ T) : Set G :=
  {g : G |
    ∃ n : N,
      QuotientGroup.mk' T n = w ∧ g ∈ conjugateSet ((n : G)⁻¹) (B : Set G)}



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


abbrev T (bn : StrictBNPair G ι M) : Subgroup bn.N :=
  titsSubgroup bn.B bn.N


abbrev WeylGroup (bn : StrictBNPair G ι M) : Type u :=
  bn.N ⧸ (T bn)


def bruhatCell (bn : StrictBNPair G ι M) (w : WeylGroup bn) : Set G :=
  bruhatCellOf bn.B bn.N (T bn) w



def subgroupGeneratedByBruhatCell (bn : StrictBNPair G ι M) (w : WeylGroup bn) :
    Subgroup G :=
  Subgroup.closure (bruhatCell bn w)


def conjugateBByInverse (bn : StrictBNPair G ι M) (w : WeylGroup bn) : Set G :=
  conjugateBByInverseOf bn.B bn.N (T bn) w



end Autoform_Buildings_and_Classical_Groups_buildings_closure_bruhatCell_contains_reduced_simples_and_eq_closure_B_union_conjugate
