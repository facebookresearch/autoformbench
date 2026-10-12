/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib





















universe u

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_20_17_goldie

noncomputable section







def IsSemiprimeRing
    (R : Type u) [Ring R] : Prop :=
  ∀ a : R, (∀ r : R, a * r * a = 0) → a = 0








abbrev IsRightNoetherianRing
    (R : Type u) [Ring R] : Prop :=
  IsNoetherianRing (MulOpposite R)




abbrev IsRightArtinianRing
    (R : Type u) [Ring R] : Prop :=
  IsArtinianRing (MulOpposite R)







def IsRegularElement
    {R : Type u} [Ring R]
    (s : R) : Prop :=
  IsLeftRegular s ∧ IsRightRegular s




def regularElementsSet
    (R : Type u) [Ring R] : Set R :=
  {s : R | IsRegularElement s}









def SatisfiesRightO1
    {R : Type u} [Ring R]
    (S : Set R) : Prop :=
  ∀ a : R, ∀ s : R, s ∈ S →
    ∃ t : R, t ∈ S ∧ ∃ b : R, a * t = s * b








def IsBookArtinianSemisimpleRing
    (Q : Type u) [Ring Q] : Prop :=
  IsArtinianRing Q ∧
    IsRightArtinianRing Q ∧
      IsSemisimpleRing Q ∧
        IsSemisimpleRing (MulOpposite Q)











structure ClassicalRightRingOfFractions
    (R : Type u) [Ring R]
    (S : Set R) where
  Q : Type u
  [ringQ : Ring Q]
  localizationMap : R →+* Q
  localizationMap_injective : Function.Injective localizationMap
  denominators_are_units :
    ∀ s : R, s ∈ S → IsUnit (localizationMap s)
  every_element_is_right_fraction :
    ∀ q : Q,
      ∃ r : R, ∃ s : R, ∃ hs : s ∈ S,
        ∃ u : Qˣ,
          localizationMap s = (u : Q) ∧
            q = localizationMap r * ((u⁻¹ : Qˣ) : Q)
  universal_property :
    ∀ (T : Type u) [Ring T] (f : R →+* T),
      (∀ s : R, s ∈ S → IsUnit (f s)) →
        ∃! g : Q →+* T, g.comp localizationMap = f

attribute [instance] ClassicalRightRingOfFractions.ringQ



end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_20_17_goldie
