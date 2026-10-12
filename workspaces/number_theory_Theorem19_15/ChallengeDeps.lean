/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped Cyclotomic NumberField BigOperators

namespace Autoform_Number_Theory_I_number_theory_Theorem19_15





















abbrev CyclotomicFieldOverQ (m : ℕ) :=
  CyclotomicField m ℚ










abbrev BookXCharacter (m : ℕ) :=
  (ZMod m)ˣ →* Units ℂ


abbrev BookXSubgroup (m : ℕ) :=
  Subgroup (BookXCharacter m)


def toDirichlet
    {m : ℕ} (χ : BookXCharacter m) : DirichletCharacter ℂ m :=
  MulChar.ofUnitHom χ


def eval
    {m : ℕ} (χ : BookXCharacter m) :
    (ZMod m)ˣ →* Units ℂ :=
  χ






def primitiveLFunction
    {m : ℕ} [NeZero m] (χ : BookXCharacter m) (s : ℂ) : ℂ := by
  classical
  let ψ : DirichletCharacter ℂ m := toDirichlet χ
  letI : NeZero ψ.conductor :=
    ⟨DirichletCharacter.conductor_ne_zero ψ⟩
  exact DirichletCharacter.LFunction ψ.primitiveCharacter s





def cyclotomicGalToZModUnits
    (m : ℕ) [NeZero m] :
    Gal(CyclotomicFieldOverQ m/ℚ) →* (ZMod m)ˣ := by
  have hm_ne_zero : m ≠ 0 := (inferInstance : NeZero m).out
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne_zero
  letI : NeZero ((m : ℕ) : ℚ) :=
    ⟨(Nat.cast_ne_zero (R := ℚ)).2 hm_ne_zero⟩
  letI : IsCyclotomicExtension {m} ℚ (CyclotomicFieldOverQ m) :=
    CyclotomicField.isCyclotomicExtension m ℚ
  exact
    (IsCyclotomicExtension.autEquivPow
      (n := m) (K := ℚ)
      (CyclotomicFieldOverQ m)
      (Polynomial.cyclotomic.irreducible_rat hm_pos)).toMonoidHom






def IsBookPhiSubgroup
    (m : ℕ) [NeZero m] (H : BookXSubgroup m)
    (Φ : Subgroup (Gal(CyclotomicFieldOverQ m/ℚ))) : Prop :=
  ∀ σ : Gal(CyclotomicFieldOverQ m/ℚ),
    σ ∈ Φ ↔
      ∀ χ : BookXCharacter m,
        χ ∈ H →
          eval χ (cyclotomicGalToZModUnits m σ) = 1



end Autoform_Number_Theory_I_number_theory_Theorem19_15
