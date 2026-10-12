/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators NumberField Topology
open Filter

namespace Autoform_Number_Theory_I_number_theory_Theorem22_20










abbrev RealInfinitePlace (K : Type*) [Field K] [NumberField K] :=
  {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w}


abbrev NonzeroIntegralIdeal (K : Type*) [Field K] [NumberField K] :=
  {I : Ideal (𝓞 K) // I ≠ ⊥}


abbrev PrimeOfNumberField (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (𝓞 K)


structure Modulus (K : Type*) [Field K] [NumberField K] where
  finitePart : NonzeroIntegralIdeal K
  infinitePart : Finset (RealInfinitePlace K)

namespace Modulus


def Dvd
    {K : Type*} [Field K] [NumberField K] (m₁ m₂ : Modulus K) : Prop :=
  m₁.finitePart.1 ∣ m₂.finitePart.1 ∧
    ∀ w ∈ m₁.infinitePart, w ∈ m₂.infinitePart

end Modulus


abbrev FracIdeal (K : Type*) [Field K] [NumberField K] :=
  FractionalIdeal (nonZeroDivisors (𝓞 K)) K


abbrev IdealGroup (K : Type*) [Field K] [NumberField K] :=
  (FracIdeal K)ˣ



namespace NonzeroIntegralIdeal


end NonzeroIntegralIdeal






def primeToNonzeroIntegralIdeal
    {K : Type*} [Field K] [NumberField K]
    (P : PrimeOfNumberField K) : NonzeroIntegralIdeal K :=
  ⟨P.asIdeal, P.ne_bot⟩


def PrincipalIdealOfUnit
    {K : Type*} [Field K] [NumberField K] (x : Kˣ) : IdealGroup K :=
  toPrincipalIdeal (𝓞 K) K x


def InKPowModulus
    {K : Type*} [Field K] [NumberField K] (m : Modulus K) (x : Kˣ) : Prop :=
  ∃ a b : 𝓞 K,
    a ≠ 0 ∧ b ≠ 0 ∧
      IsCoprime (Ideal.span ({a} : Set (𝓞 K))) m.finitePart.1 ∧
        IsCoprime (Ideal.span ({b} : Set (𝓞 K))) m.finitePart.1 ∧
          ((a : 𝓞 K) : K) = (x : K) * (b : K)


def InKPowModulusOne
    {K : Type*} [Field K] [NumberField K] (m : Modulus K) (x : Kˣ) : Prop :=
  InKPowModulus m x ∧
    (∀ a b : 𝓞 K,
      a ≠ 0 → b ≠ 0 →
        IsCoprime (Ideal.span ({a} : Set (𝓞 K))) m.finitePart.1 →
          IsCoprime (Ideal.span ({b} : Set (𝓞 K))) m.finitePart.1 →
            ((a : 𝓞 K) : K) = (x : K) * (b : K) →
              a - b ∈ m.finitePart.1) ∧
      ∀ w ∈ m.infinitePart,
        0 < NumberField.InfinitePlace.embedding_of_isReal w.2 (x : K)




























namespace CongruenceSubgroup




end CongruenceSubgroup






namespace RayClassCharacter















def classNumberStrip (K : Type*) [Field K] [NumberField K] : Set ℂ :=
  {s : ℂ | 1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ) < s.re}


def AtMostSimplePoleAt (F : ℂ → ℂ) (z : ℂ) : Prop :=
  MeromorphicAt F z ∧ meromorphicOrderAt F z ≠ ⊤ ∧
    ((-1 : WithTop ℤ) ≤ meromorphicOrderAt F z)





end RayClassCharacter



def PrimeDirichletSeriesTerm
    {K : Type*} [Field K] [NumberField K]
    (S : Set (PrimeOfNumberField K)) (P : PrimeOfNumberField K) (x : ℝ) : ℝ := by
  classical
  exact if _h : P ∈ S then
    Real.exp (-x * Real.log (Ideal.absNorm P.asIdeal : ℝ))
  else
    0


def PrimeDirichletSeriesConverges
    {K : Type*} [Field K] [NumberField K]
    (S : Set (PrimeOfNumberField K)) : Prop :=
  ∀ x : ℝ, 1 < x → Summable fun P : PrimeOfNumberField K => PrimeDirichletSeriesTerm S P x


def PrimeDirichletSeries
    {K : Type*} [Field K] [NumberField K]
    (S : Set (PrimeOfNumberField K)) (x : ℝ) : ℝ :=
  ∑' P : PrimeOfNumberField K, PrimeDirichletSeriesTerm S P x


def HasDirichletDensity
    {K : Type*} [Field K] [NumberField K]
    (S : Set (PrimeOfNumberField K)) (d : ℝ) : Prop :=
  PrimeDirichletSeriesConverges S ∧
    Filter.Tendsto
      (fun x : ℝ => PrimeDirichletSeries S x / Real.log (1 / (x - 1)))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds d)



end Autoform_Number_Theory_I_number_theory_Theorem22_20

end
