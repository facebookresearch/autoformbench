import Mathlib

noncomputable section

open scoped BigOperators NumberField Topology
open Filter

namespace Autoform_Number_Theory_I_number_theory_Proposition22_19



























abbrev RealInfinitePlace (K : Type*) [Field K] [NumberField K] :=
  {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w}


abbrev NonzeroIntegralIdeal (K : Type*) [Field K] [NumberField K] :=
  {I : Ideal (𝓞 K) // I ≠ ⊥}


structure Modulus (K : Type*) [Field K] [NumberField K] where
  finitePart : NonzeroIntegralIdeal K
  infinitePart : Finset (RealInfinitePlace K)


abbrev FracIdeal (K : Type*) [Field K] [NumberField K] :=
  FractionalIdeal (nonZeroDivisors (𝓞 K)) K


abbrev IdealGroup (K : Type*) [Field K] [NumberField K] :=
  (FracIdeal K)ˣ









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


def InKPowModulusOneBookValuation
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


abbrev InKPowModulusOne
    {K : Type*} [Field K] [NumberField K] (m : Modulus K) (x : Kˣ) : Prop :=
  InKPowModulusOneBookValuation m x




















namespace RayClassCharacter








def weberContinuationDomain
    (K : Type*) [Field K] [NumberField K] : Set ℂ :=
  {s : ℂ | 1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ) < s.re}


def AtMostSimplePoleAt (F : ℂ → ℂ) (z : ℂ) : Prop :=
  MeromorphicAt F z ∧ meromorphicOrderAt F z ≠ ⊤ ∧
    ((-1 : WithTop ℤ) ≤ meromorphicOrderAt F z)

end RayClassCharacter



end Autoform_Number_Theory_I_number_theory_Proposition22_19

end
