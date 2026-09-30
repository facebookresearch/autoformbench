import Mathlib

noncomputable section

open scoped NumberField

namespace Autoform_Number_Theory_I_number_theory_Theorem21_8














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


def InKPowModulusOne
    {K : Type*} [Field K] [NumberField K] (m : Modulus K) (x : Kˣ) : Prop :=
  InKPowModulus m x ∧
    (∀ a b : 𝓞 K,
      a ≠ 0 → b ≠ 0 →
        IsCoprime (Ideal.span ({a} : Set (𝓞 K))) m.finitePart.1 →
          IsCoprime (Ideal.span ({b} : Set (𝓞 K))) m.finitePart.1 →
            ((a : 𝓞 K) : K) = (x : K) * (b : K) →
              a - b ∈ m.finitePart.1) ∧
      ∀ w ∈ m.infinitePart, 0 < NumberField.InfinitePlace.embedding_of_isReal w.2 x











































abbrev OrdinaryClassGroup (K : Type*) [Field K] [NumberField K] :=
  ClassGroup (𝓞 K)


def unitToFieldUnit
    (K : Type*) [Field K] [NumberField K] : (𝓞 K)ˣ →* Kˣ :=
  Units.map (algebraMap (𝓞 K) K)



































def classGroupToUnit
    (K : Type*) [Field K] [NumberField K] : OrdinaryClassGroup K →* Unit where
  toFun _ := ()
  map_one' := rfl
  map_mul' := by intro _ _; rfl





abbrev SignResidueGroup
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :=
  ({w : RealInfinitePlace K // w ∈ m.infinitePart} → ℤˣ) ×
    ((𝓞 K) ⧸ m.finitePart.1)ˣ











end Autoform_Number_Theory_I_number_theory_Theorem21_8

end