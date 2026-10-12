/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/





import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ENat.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Norm.Basic
import Submission
import ChallengeDeps
universe u v

noncomputable section

open scoped Polynomial

namespace Autoform_Number_Theory_I_number_theory_Theorem11_19_in_particular





























theorem Theorem11_19
    {K : Type u} [NormedField K]
    (A : Subring K)
    [IsFractionRing A K]
    [IsDiscreteValuationRing A]
    [CompleteSpace A]
    (c : ℝ)
    (hK : DVRNormCompatible (K := K) A c)
    (f : K[X])
    (hf_monic : f.Monic)
    (hf_irred : Irreducible f)
    (hf_sep : f.Separable) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {Ω : Type v} [NormedField Ω] [NormedAlgebra K Ω]
        [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω],
      IsExtendedAbsoluteValue (K := K) (Ω := Ω) →
      ∀ g : K[X], g.Monic → polynomialL1Norm (f - g) < δ →
        ∀ β : Ω, β ∈ g.rootSet Ω →
          ∃ α : Ω,
            α ∈ f.rootSet Ω ∧
              RootBelongsTo (K := K) β α ∧
                IntermediateField.adjoin K ({β} : Set Ω) =
                  IntermediateField.adjoin K ({α} : Set Ω) := Submission.Autoform_Number_Theory_I_number_theory_Theorem11_19_in_particular.Theorem11_19 A c hK f hf_monic hf_irred hf_sep






theorem Theorem11_19_in_particular
    {K : Type u} [NormedField K]
    (A : Subring K)
    [IsFractionRing A K]
    [IsDiscreteValuationRing A]
    [CompleteSpace A]
    (c : ℝ)
    (hK : DVRNormCompatible (K := K) A c)
    (f : K[X])
    (hf_monic : f.Monic)
    (hf_irred : Irreducible f)
    (hf_sep : f.Separable) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {Ω : Type v} [NormedField Ω] [NormedAlgebra K Ω]
        [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω],
      IsExtendedAbsoluteValue (K := K) (Ω := Ω) →
      ∀ g : K[X], g.Monic → polynomialL1Norm (f - g) < δ →
        g.Separable ∧
          Irreducible g ∧
            SameSplittingField (K := K) (Ω := Ω) g f := Submission.Autoform_Number_Theory_I_number_theory_Theorem11_19_in_particular.Theorem11_19_in_particular A c hK f hf_monic hf_irred hf_sep

end Autoform_Number_Theory_I_number_theory_Theorem11_19_in_particular

end
