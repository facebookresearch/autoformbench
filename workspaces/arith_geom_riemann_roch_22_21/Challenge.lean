/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps




import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_riemann_roch_22_21























noncomputable section

open scoped BigOperators

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_riemann_roch_22_21

theorem map_neg {F : Type*} [Field F] (v : NormalizedDiscreteValuation F) (x : F) :
    v (-x) = v x := by
  
  sorry


theorem ring_add_mem {F : Type*} [Field F] (v : NormalizedDiscreteValuation F)
    (x y : F) (hx : (0 : WithTop ℤ) ≤ v x) (hy : (0 : WithTop ℤ) ≤ v y) :
    (0 : WithTop ℤ) ≤ v (x + y) := by
  
  sorry


theorem ring_mul_mem {F : Type*} [Field F] (v : NormalizedDiscreteValuation F)
    (x y : F) (hx : (0 : WithTop ℤ) ≤ v x) (hy : (0 : WithTop ℤ) ≤ v y) :
    (0 : WithTop ℤ) ≤ v (x * y) := by
  
  sorry

namespace NormalizedDiscreteValuation

variable {F : Type*} [Field F] (v : NormalizedDiscreteValuation F)


def ring : Subring F where
  carrier := { x : F | (0 : WithTop ℤ) ≤ v x }
  zero_mem' := by
    simp
  one_mem' := by
    simp
  add_mem' := by
    intro x y hx hy
    exact ring_add_mem v x y hx hy
  neg_mem' := by
    intro x hx
    simpa [map_neg v x] using hx
  mul_mem' := by
    intro x y hx hy
    exact ring_mul_mem v x y hx hy

end NormalizedDiscreteValuation


theorem maximalIdeal_add_mem {F : Type*} [Field F] (v : NormalizedDiscreteValuation F)
    (x y : v.ring) (hx : (0 : WithTop ℤ) < v x.1) (hy : (0 : WithTop ℤ) < v y.1) :
    (0 : WithTop ℤ) < v (x + y).1 := by
  
  sorry


theorem maximalIdeal_smul_mem {F : Type*} [Field F] (v : NormalizedDiscreteValuation F)
    (a x : v.ring) (hx : (0 : WithTop ℤ) < v x.1) :
    (0 : WithTop ℤ) < v (a • x).1 := by
  
  sorry

namespace NormalizedDiscreteValuation

variable {F : Type*} [Field F] (v : NormalizedDiscreteValuation F)


def maximalIdeal : Ideal v.ring where
  carrier := { x : v.ring | (0 : WithTop ℤ) < v x.1 }
  zero_mem' := by
    simp
  add_mem' := by
    intro x y hx hy
    exact maximalIdeal_add_mem v x y hx hy
  smul_mem' := by
    intro a x hx
    exact maximalIdeal_smul_mem v a x hx

end NormalizedDiscreteValuation


theorem maximalIdeal_isMaximal {F : Type*} [Field F]
    (v : NormalizedDiscreteValuation F) : v.maximalIdeal.IsMaximal := by
  sorry

namespace NormalizedDiscreteValuation

variable {F : Type*} [Field F] (v : NormalizedDiscreteValuation F)


abbrev residueField : Type _ :=
  v.ring ⧸ v.maximalIdeal

noncomputable instance residueFieldField : Field v.residueField := by
  haveI : v.maximalIdeal.IsMaximal := maximalIdeal_isMaximal v
  exact Ideal.Quotient.field v.maximalIdeal

end NormalizedDiscreteValuation


def constantsToValuationRing {k F : Type*} [Field k] [Field F] [Algebra k F]
    (v : NormalizedDiscreteValuation F)
    (hconst : ∀ c : k, c ≠ 0 → v (algebraMap k F c) = (0 : WithTop ℤ)) :
    k →+* v.ring := by
  classical
  refine
    { toFun := fun c =>
        ⟨algebraMap k F c, by
          by_cases hc : c = 0
          · subst c
            simp [NormalizedDiscreteValuation.ring]
          · change (0 : WithTop ℤ) ≤ v (algebraMap k F c)
            rw [hconst c hc]⟩
      map_zero' := by
        ext
        simp
      map_one' := by
        ext
        simp
      map_add' := by
        intro x y
        ext
        simp
      map_mul' := by
        intro x y
        ext
        simp }


@[reducible]
noncomputable def residueAlgebraOfTrivialConstants
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (v : NormalizedDiscreteValuation F)
    (hconst : ∀ c : k, c ≠ 0 → v (algebraMap k F c) = (0 : WithTop ℤ)) :
    Algebra k v.residueField :=
  RingHom.toAlgebra
    ((Ideal.Quotient.mk v.maximalIdeal).comp
      (constantsToValuationRing v hconst))

namespace FunctionFieldCurve


abbrev ResidueField {k : Type*} [Field k] (C : FunctionFieldCurve k)
    (P : C.Place) : Type _ :=
  (C.placeValuation P).residueField

noncomputable instance instFieldResidueField {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) : Field (C.ResidueField P) :=
  NormalizedDiscreteValuation.residueFieldField (C.placeValuation P)

noncomputable instance instAlgebraResidueField {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) : Algebra k (C.ResidueField P) :=
  residueAlgebraOfTrivialConstants (C.placeValuation P)
    (C.place_trivial_on_constants P)

end FunctionFieldCurve


theorem residueField_finiteDimensional {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) :
    FiniteDimensional k (C.ResidueField P) := by
  sorry

namespace FunctionFieldCurve


def residueDegree {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) : ℕ :=
  letI : FiniteDimensional k (C.ResidueField P) := residueField_finiteDimensional C P
  Module.finrank k (C.ResidueField P)

end FunctionFieldCurve


def divisorDegree {k : Type*} [Field k] (C : FunctionFieldCurve k)
    (D : Divisor C) : ℤ :=
  D.sum fun P n => n * (C.residueDegree P : ℤ)



theorem riemannRochSpace_add_mem {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (D : Divisor C) (f g : C.F)
    (hf : ∀ P : C.Place, ((-D P : ℤ) : WithTop ℤ) ≤ ord C P f)
    (hg : ∀ P : C.Place, ((-D P : ℤ) : WithTop ℤ) ≤ ord C P g) :
    ∀ P : C.Place, ((-D P : ℤ) : WithTop ℤ) ≤ ord C P (f + g) := by
  
  sorry



theorem riemannRochSpace_smul_mem {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (D : Divisor C) (c : k) (f : C.F)
    (hf : ∀ P : C.Place, ((-D P : ℤ) : WithTop ℤ) ≤ ord C P f) :
    ∀ P : C.Place, ((-D P : ℤ) : WithTop ℤ) ≤ ord C P (c • f) := by
  
  sorry


def RiemannRochSpace {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (D : Divisor C) : Submodule k C.F where
  carrier := { f : C.F | ∀ P : C.Place, ((-D P : ℤ) : WithTop ℤ) ≤ ord C P f }
  zero_mem' := by
    intro P
    simp [ord]
  add_mem' := by
    intro f g hf hg P
    exact riemannRochSpace_add_mem C D f g hf hg P
  smul_mem' := by
    intro c f hf P
    exact riemannRochSpace_smul_mem C D c f hf P


theorem riemannRochSpace_finiteDimensional
    {k : Type*} [Field k] (C : FunctionFieldCurve k) (D : Divisor C) :
    FiniteDimensional k (RiemannRochSpace C D) := by
  sorry


def ell {k : Type*} [Field k] (C : FunctionFieldCurve k) (D : Divisor C) : ℤ :=
  letI : FiniteDimensional k (RiemannRochSpace C D) :=
    riemannRochSpace_finiteDimensional C D
  (Module.finrank k (RiemannRochSpace C D) : ℤ)


def rIndex {k : Type*} [Field k] (C : FunctionFieldCurve k) (D : Divisor C) : ℤ :=
  divisorDegree C D - ell C D


def genusValues {k : Type*} [Field k] (C : FunctionFieldCurve k) : Set ℤ :=
  Set.range fun D : Divisor C => rIndex C D + 1


def IsGenus {k : Type*} [Field k] (C : FunctionFieldCurve k) (g : ℕ) : Prop :=
  IsGreatest (genusValues C) (g : ℤ)



theorem localCauchySeq_const_cauchy {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) (f : C.F) :
    ∀ n : ℤ, ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      (n : WithTop ℤ) ≤ ord C P (f - f) := by
  
  sorry


theorem localCauchySeq_add_cauchy {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) (s t : LocalCauchySeq C P) :
    ∀ n : ℤ, ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      (n : WithTop ℤ) ≤ ord C P (s.seq i + t.seq i - (s.seq j + t.seq j)) := by
  
  sorry


theorem localCauchySeq_smulBase_cauchy {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) (c : k) (s : LocalCauchySeq C P) :
    ∀ n : ℤ, ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      (n : WithTop ℤ) ≤
        ord C P (algebraMap k C.F c * s.seq i - algebraMap k C.F c * s.seq j) := by
  
  sorry

namespace LocalCauchySeq

variable {k : Type*} [Field k] {C : FunctionFieldCurve k} {P : C.Place}


def const (f : C.F) : LocalCauchySeq C P where
  seq := fun _ => f
  cauchy := localCauchySeq_const_cauchy C P f


def add (s t : LocalCauchySeq C P) : LocalCauchySeq C P where
  seq := fun i => s.seq i + t.seq i
  cauchy := localCauchySeq_add_cauchy C P s t


def smulBase (c : k) (s : LocalCauchySeq C P) : LocalCauchySeq C P where
  seq := fun i => algebraMap k C.F c * s.seq i
  cauchy := localCauchySeq_smulBase_cauchy C P c s

end LocalCauchySeq


theorem localCauchySeqEquivalent_refl {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) (s : LocalCauchySeq C P) :
    LocalCauchySeqEquivalent s s := by
  
  sorry


theorem localCauchySeqEquivalent_symm {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) (s t : LocalCauchySeq C P)
    (h : LocalCauchySeqEquivalent s t) : LocalCauchySeqEquivalent t s := by
  
  sorry


theorem localCauchySeqEquivalent_trans {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) (s t u : LocalCauchySeq C P)
    (hst : LocalCauchySeqEquivalent s t) (htu : LocalCauchySeqEquivalent t u) :
    LocalCauchySeqEquivalent s u := by
  
  sorry


def localCauchySeqSetoid {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) : Setoid (LocalCauchySeq C P) where
  r := fun s t => LocalCauchySeqEquivalent (C := C) (P := P) s t
  iseqv := by
    constructor
    · intro s
      exact localCauchySeqEquivalent_refl C P s
    · intro s t h
      exact localCauchySeqEquivalent_symm C P s t h
    · intro s t u hst htu
      exact localCauchySeqEquivalent_trans C P s t u hst htu


def LocalCompletion {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) : Type _ :=
  Quotient (localCauchySeqSetoid C P)


def localCompletionOfFunction {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) (f : C.F) : LocalCompletion C P :=
  Quotient.mk (localCauchySeqSetoid C P) (LocalCauchySeq.const f)


theorem localCompletionAdd_respects {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place)
    (s₁ s₂ t₁ t₂ : LocalCauchySeq C P)
    (hs : LocalCauchySeqEquivalent s₁ t₁) (ht : LocalCauchySeqEquivalent s₂ t₂) :
    Quotient.mk (localCauchySeqSetoid C P) (LocalCauchySeq.add s₁ s₂) =
      Quotient.mk (localCauchySeqSetoid C P) (LocalCauchySeq.add t₁ t₂) := by
  
  sorry


def localCompletionAdd {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place)
    (x y : LocalCompletion C P) : LocalCompletion C P :=
  Quotient.lift₂
    (fun s t : LocalCauchySeq C P =>
      Quotient.mk (localCauchySeqSetoid C P) (LocalCauchySeq.add s t))
    (by
      intro s₁ s₂ t₁ t₂ hs ht
      exact localCompletionAdd_respects C P s₁ s₂ t₁ t₂ hs ht)
    x y


theorem localCompletionSMul_respects {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) (c : k)
    (s t : LocalCauchySeq C P) (h : LocalCauchySeqEquivalent s t) :
    Quotient.mk (localCauchySeqSetoid C P) (LocalCauchySeq.smulBase c s) =
      Quotient.mk (localCauchySeqSetoid C P) (LocalCauchySeq.smulBase c t) := by
  
  sorry


def localCompletionSMul {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) (c : k)
    (x : LocalCompletion C P) : LocalCompletion C P :=
  Quotient.lift
    (fun s : LocalCauchySeq C P =>
      Quotient.mk (localCauchySeqSetoid C P) (LocalCauchySeq.smulBase c s))
    (by
      intro s t h
      exact localCompletionSMul_respects C P c s t h)
    x


theorem localCompletionValuationAtLeast_respects {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) (n : ℤ)
    (s t : LocalCauchySeq C P) (h : LocalCauchySeqEquivalent s t) :
    (∃ N : ℕ, ∀ i : ℕ, N ≤ i → (n : WithTop ℤ) ≤ ord C P (s.seq i)) ↔
      (∃ N : ℕ, ∀ i : ℕ, N ≤ i → (n : WithTop ℤ) ≤ ord C P (t.seq i)) := by
  
  sorry


def LocalCompletionValuationAtLeast {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) (n : ℤ)
    (x : LocalCompletion C P) : Prop :=
  Quotient.lift
    (fun s : LocalCauchySeq C P =>
      ∃ N : ℕ, ∀ i : ℕ, N ≤ i → (n : WithTop ℤ) ≤ ord C P (s.seq i))
    (by
      intro s t h
      apply propext
      exact localCompletionValuationAtLeast_respects C P n s t h)
    x


structure Adele {k : Type*} [Field k] (C : FunctionFieldCurve k) where
  component : ∀ P : C.Place, LocalCompletion C P
  finite_nonintegral :
    { P : C.Place | ¬ LocalCompletionValuationAtLeast C P 0 (component P) }.Finite


theorem adele_zero_finite_nonintegral {k : Type*} [Field k]
    (C : FunctionFieldCurve k) :
    { P : C.Place | ¬ LocalCompletionValuationAtLeast C P 0
        (localCompletionOfFunction C P 0) }.Finite := by
  
  sorry



theorem adele_add_finite_nonintegral {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (α β : Adele C) :
    { P : C.Place | ¬ LocalCompletionValuationAtLeast C P 0
        (localCompletionAdd C P (α.component P) (β.component P)) }.Finite := by
  
  
  sorry



theorem adele_smul_finite_nonintegral {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (c : k) (α : Adele C) :
    { P : C.Place | ¬ LocalCompletionValuationAtLeast C P 0
        (localCompletionSMul C P c (α.component P)) }.Finite := by
  
  
  sorry

namespace Adele

variable {k : Type*} [Field k] {C : FunctionFieldCurve k}


def zero (C : FunctionFieldCurve k) : Adele C where
  component := fun P => localCompletionOfFunction C P 0
  finite_nonintegral := adele_zero_finite_nonintegral C


def add (α β : Adele C) : Adele C where
  component := fun P => localCompletionAdd C P (α.component P) (β.component P)
  finite_nonintegral := adele_add_finite_nonintegral C α β


def smul (c : k) (α : Adele C) : Adele C where
  component := fun P => localCompletionSMul C P c (α.component P)
  finite_nonintegral := adele_smul_finite_nonintegral C c α

end Adele


theorem principalAdele_finite_nonintegral {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (f : C.F) :
    { P : C.Place | ¬ LocalCompletionValuationAtLeast C P 0
        (localCompletionOfFunction C P f) }.Finite := by
  
  sorry


def principalAdele {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (f : C.F) : Adele C where
  component := fun P => localCompletionOfFunction C P f
  finite_nonintegral := principalAdele_finite_nonintegral C f


def AdeleSpace {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (D : Divisor C) (α : Adele C) : Prop :=
  ∀ P : C.Place,
    LocalCompletionValuationAtLeast C P (-D P) (α.component P)


def InAdeleSpacePlusPrincipal {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (D : Divisor C) (α : Adele C) : Prop :=
  ∃ β : Adele C, ∃ f : C.F,
    AdeleSpace C D β ∧ α = Adele.add β (principalAdele C f)


structure WeilFunctional {k : Type*} [Field k] (C : FunctionFieldCurve k) where
  toFun : Adele C → k
  map_add' : ∀ α β : Adele C, toFun (Adele.add α β) = toFun α + toFun β
  map_smul' : ∀ (c : k) (α : Adele C), toFun (Adele.smul c α) = c * toFun α

instance instCoeFunWeilFunctional {k : Type*} [Field k] {C : FunctionFieldCurve k} :
    CoeFun (WeilFunctional C) (fun _ => Adele C → k) where
  coe ω := ω.toFun


def WeilFunctionalInOmega {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (ω : WeilFunctional C) (D : Divisor C) : Prop :=
  ∀ α : Adele C, InAdeleSpacePlusPrincipal C D α → ω α = 0


structure WeilDifferential {k : Type*} [Field k] (C : FunctionFieldCurve k) where
  functional : WeilFunctional C
  exists_inOmega : ∃ D : Divisor C, WeilFunctionalInOmega C functional D


def WeilDifferentialNonzero {k : Type*} [Field k]
    {C : FunctionFieldCurve k} (ω : WeilDifferential C) : Prop :=
  ∃ α : Adele C, ω.functional α ≠ 0


def HasDifferentialDivisor {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (ω : WeilDifferential C) (W : Divisor C) : Prop :=
  WeilDifferentialNonzero ω ∧
    WeilFunctionalInOmega C ω.functional W ∧
      ∀ D : Divisor C, WeilFunctionalInOmega C ω.functional D → DivisorLe D W


def IsCanonicalDivisor {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (W : Divisor C) : Prop :=
  ∃ ω : WeilDifferential C, HasDifferentialDivisor C ω W









theorem riemann_roch_22_21
    {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (g : ℕ) (hg : IsGenus C g)
    (W : Divisor C) (hW : IsCanonicalDivisor C W)
    (D : Divisor C) :
    ell C D = divisorDegree C D + 1 - (g : ℤ) + ell C (W - D) := by
  sorry

end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_riemann_roch_22_21

end
