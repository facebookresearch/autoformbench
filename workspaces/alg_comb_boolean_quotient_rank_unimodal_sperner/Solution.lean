/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission
import ChallengeDeps

open Autoform_Algebraic_Combinatorics_alg_comb_boolean_quotient_rank_unimodal_sperner
open scoped BigOperators

namespace Autoform_Algebraic_Combinatorics_alg_comb_boolean_quotient_rank_unimodal_sperner

noncomputable section







theorem permuteSubset_subset_iff {n : ℕ}
    (σ : Equiv.Perm (Fin n))
    {A B : BooleanAlgebra n} :
    permuteSubset σ A ⊆ permuteSubset σ B ↔ A ⊆ B := by apply Submission.Autoform_Algebraic_Combinatorics_alg_comb_boolean_quotient_rank_unimodal_sperner.permuteSubset_subset_iff <;> assumption

theorem permuteSubset_comp {n : ℕ}
    (σ τ : Equiv.Perm (Fin n))
    (A : BooleanAlgebra n) :
    permuteSubset (σ * τ) A =
      permuteSubset σ (permuteSubset τ A) := by
  classical
  ext x
  simp [permuteSubset, Equiv.Perm.coe_mul]




theorem orbitSetoid_symm (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (A B : BooleanAlgebra n) (σ : G)
    (hσ : permuteSubset (σ : Equiv.Perm (Fin n)) A = B) :
    permuteSubset ((σ⁻¹ : G) : Equiv.Perm (Fin n)) B = A := by apply Submission.Autoform_Algebraic_Combinatorics_alg_comb_boolean_quotient_rank_unimodal_sperner.orbitSetoid_symm <;> assumption


theorem orbitSetoid_trans (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (A B C : BooleanAlgebra n) (σ τ : G)
    (hσ : permuteSubset (σ : Equiv.Perm (Fin n)) A = B)
    (hτ : permuteSubset (τ : Equiv.Perm (Fin n)) B = C) :
    permuteSubset ((τ * σ : G) : Equiv.Perm (Fin n)) A = C := by apply Submission.Autoform_Algebraic_Combinatorics_alg_comb_boolean_quotient_rank_unimodal_sperner.orbitSetoid_trans <;> assumption







def orbitSetoid (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n))) :
    Setoid (BooleanAlgebra n) where
  r := SameOrbit G
  iseqv := by
    classical
    constructor
    · intro A
      refine ⟨1, ?_⟩
      ext x
      simp [SameOrbit, permuteSubset]
    · intro A B h
      rcases h with ⟨σ, hσ⟩
      exact ⟨σ⁻¹, orbitSetoid_symm n G A B σ hσ⟩
    · intro A B C hAB hBC
      rcases hAB with ⟨σ, hσ⟩
      rcases hBC with ⟨τ, hτ⟩
      exact ⟨τ * σ, orbitSetoid_trans n G A B C σ τ hσ hτ⟩


abbrev BooleanQuotient
    (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n))) : Type :=
  Quotient (orbitSetoid n G)
instance instDecidableEqBooleanQuotient (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) :
    DecidableEq (BooleanQuotient n G) :=
  Classical.decEq _







def orbitMk {n : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (A : BooleanAlgebra n) : BooleanQuotient n G :=
  Quotient.mk (orbitSetoid n G) A






def QuotientLe {n : ℕ}
    {G : Subgroup (Equiv.Perm (Fin n))}
    (O O' : BooleanQuotient n G) : Prop :=
  ∃ A B : BooleanAlgebra n,
    orbitMk G A = O ∧
    orbitMk G B = O' ∧
    A ⊆ B
theorem QuotientPartialOrder (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) :
  IsPartialOrder (BooleanQuotient n G) QuotientLe := by apply Submission.Autoform_Algebraic_Combinatorics_alg_comb_boolean_quotient_rank_unimodal_sperner.QuotientPartialOrder <;> assumption





















def QuotientCovers {n : ℕ}
    {G : Subgroup (Equiv.Perm (Fin n))}
    (O O' : BooleanQuotient n G) : Prop :=
  QuotientLe O O' ∧
  O ≠ O' ∧
  ∀ Q : BooleanQuotient n G,
    QuotientLe O Q →
    QuotientLe Q O' →
    Q = O ∨ Q = O'


def quotientRank {n : ℕ}
    {G : Subgroup (Equiv.Perm (Fin n))}
    (O : BooleanQuotient n G) : ℕ :=
  Quotient.liftOn O
    (fun A : BooleanAlgebra n => A.card)
    (by
      intro A B h
      rcases h with ⟨σ, hσ⟩
      rw [← hσ]
      symm
      exact permuteSubset_card (σ : Equiv.Perm (Fin n)) A)


def QuotientRankLevel
    (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (i : ℕ) : Type :=
  {O : BooleanQuotient n G // quotientRank O = i}


def quotientRankNumber
    (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (i : ℕ) : ℕ :=
  Nat.card (QuotientRankLevel n G i)





def IsGradedOfRank
    (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  (∀ O : BooleanQuotient n G, quotientRank O ≤ n) ∧
  (∃ O : BooleanQuotient n G, quotientRank O = 0) ∧
  (∃ O : BooleanQuotient n G, quotientRank O = n) ∧
  (∀ O O' : BooleanQuotient n G,
    QuotientCovers O O' →
      quotientRank O' = quotientRank O + 1)


def IsRankSymmetric
    (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∀ i : ℕ,
    i ≤ n →
      quotientRankNumber n G i =
        quotientRankNumber n G (n - i)


def IsRankUnimodal
    (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  (∀ i : ℕ,
    2 * i + 2 ≤ n →
      quotientRankNumber n G i ≤
        quotientRankNumber n G (i + 1)) ∧
  (∀ i : ℕ,
    i + 1 ≤ n →
    n ≤ 2 * i →
      quotientRankNumber n G (i + 1) ≤
        quotientRankNumber n G i)


def IsQuotientAntichain
    {n : ℕ}
    {G : Subgroup (Equiv.Perm (Fin n))}
    (A : Finset (BooleanQuotient n G)) : Prop :=
  ∀ ⦃O O' : BooleanQuotient n G⦄,
    O ∈ A →
    O' ∈ A →
    O ≠ O' →
      ¬ QuotientLe O O' ∧ ¬ QuotientLe O' O






def HasSpernerProperty
    (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∀ A : Finset (BooleanQuotient n G),
    IsQuotientAntichain A →
      ∃ i : ℕ,
        i ≤ n ∧
        A.card ≤ quotientRankNumber n G i


theorem boolean_quotient_rank_unimodal_sperner
    (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n))) :
    IsGradedOfRank n G ∧
    IsRankSymmetric n G ∧
    IsRankUnimodal n G ∧
    HasSpernerProperty n G := by apply Submission.Autoform_Algebraic_Combinatorics_alg_comb_boolean_quotient_rank_unimodal_sperner.boolean_quotient_rank_unimodal_sperner <;> assumption

end

end Autoform_Algebraic_Combinatorics_alg_comb_boolean_quotient_rank_unimodal_sperner
