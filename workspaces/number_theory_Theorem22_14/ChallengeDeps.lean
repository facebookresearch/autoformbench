/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped NumberField

namespace Autoform_Number_Theory_I_number_theory_Theorem22_14










abbrev RealInfinitePlace (K : Type*) [Field K] [NumberField K] :=
  {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w}


abbrev NonzeroIntegralIdeal (K : Type*) [Field K] [NumberField K] :=
  {I : Ideal (𝓞 K) // I ≠ ⊥}








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
      ∀ w ∈ m.infinitePart, 0 < NumberField.InfinitePlace.embedding_of_isReal w.2 (x : K)




























namespace CongruenceSubgroup



end CongruenceSubgroup



namespace CongruenceSubgroup


end CongruenceSubgroup




namespace RayClassCharacter



end RayClassCharacter











namespace RayClassCharacter



end RayClassCharacter







end Autoform_Number_Theory_I_number_theory_Theorem22_14

end
