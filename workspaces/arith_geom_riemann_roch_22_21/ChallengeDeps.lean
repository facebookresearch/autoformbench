import Mathlib
























noncomputable section

open scoped BigOperators

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_riemann_roch_22_21


structure NormalizedDiscreteValuation (F : Type*) [Field F] where
  toFun : F → WithTop ℤ
  map_zero' : toFun 0 = ⊤
  map_one' : toFun 1 = (0 : WithTop ℤ)
  map_mul' : ∀ x y : F, toFun (x * y) = toFun x + toFun y
  map_add' : ∀ x y : F, min (toFun x) (toFun y) ≤ toFun (x + y)
  finite_ne_zero' : ∀ {x : F}, x ≠ 0 → ∃ n : ℤ, toFun x = (n : WithTop ℤ)
  exists_uniformizer' : ∃ t : F, toFun t = (1 : WithTop ℤ)

instance instCoeFunNormalizedDiscreteValuation {F : Type*} [Field F] :
    CoeFun (NormalizedDiscreteValuation F) (fun _ => F → WithTop ℤ) where
  coe v := v.toFun

namespace NormalizedDiscreteValuation

variable {F : Type*} [Field F] (v : NormalizedDiscreteValuation F)

@[simp] theorem map_zero : v 0 = ⊤ := v.map_zero'
@[simp] theorem map_one : v 1 = (0 : WithTop ℤ) := v.map_one'
theorem map_mul (x y : F) : v (x * y) = v x + v y := v.map_mul' x y
theorem map_add (x y : F) : min (v x) (v y) ≤ v (x + y) := v.map_add' x y

end NormalizedDiscreteValuation


class IsOneVariableFunctionField
    (k F : Type*) [Field k] [Field F] [Algebra k F] : Prop where
  exists_finite_transcendence_generator :
    ∃ x : F,
      ¬ IsAlgebraic k x ∧
        FiniteDimensional (↥(IntermediateField.adjoin k ({x} : Set F))) F
  constants_algebraically_closed :
    ∀ x : F, IsAlgebraic k x → ∃ c : k, algebraMap k F c = x






structure FunctionFieldCurve (k : Type*) [Field k] where
  baseFieldPerfect : PerfectField k
  F : Type*
  fieldF : Field F
  algebraF : Algebra k F
  isFunctionField : IsOneVariableFunctionField k F

namespace FunctionFieldCurve

instance instFieldF {k : Type*} [Field k] (C : FunctionFieldCurve k) : Field C.F := C.fieldF
instance instAlgebraF {k : Type*} [Field k] (C : FunctionFieldCurve k) : Algebra k C.F :=
  C.algebraF
instance instIsOneVariableFunctionField {k : Type*} [Field k] (C : FunctionFieldCurve k) :
    IsOneVariableFunctionField k C.F := C.isFunctionField


abbrev Place {k : Type*} [Field k] (C : FunctionFieldCurve k) : Type _ :=
  { v : NormalizedDiscreteValuation C.F //
      ∀ c : k, c ≠ 0 → v (algebraMap k C.F c) = (0 : WithTop ℤ) }


abbrev placeValuation {k : Type*} [Field k] (C : FunctionFieldCurve k)
    (P : C.Place) : NormalizedDiscreteValuation C.F :=
  P.1


theorem place_trivial_on_constants {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) :
    ∀ c : k, c ≠ 0 → C.placeValuation P (algebraMap k C.F c) = (0 : WithTop ℤ) :=
  P.2

end FunctionFieldCurve


abbrev ord {k : Type*} [Field k] (C : FunctionFieldCurve k)
    (P : C.Place) (f : C.F) : WithTop ℤ :=
  C.placeValuation P f


abbrev Divisor {k : Type*} [Field k] (C : FunctionFieldCurve k) : Type _ :=
  C.Place →₀ ℤ


def DivisorLe {k : Type*} [Field k] {C : FunctionFieldCurve k}
    (D E : Divisor C) : Prop :=
  ∀ P : C.Place, D P ≤ E P




structure LocalCauchySeq {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) where
  seq : ℕ → C.F
  cauchy :
    ∀ n : ℤ, ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      (n : WithTop ℤ) ≤ ord C P (seq i - seq j)


def LocalSeqTendsToZero {k : Type*} [Field k]
    {C : FunctionFieldCurve k} {P : C.Place} (s : ℕ → C.F) : Prop :=
  ∀ n : ℤ, ∃ N : ℕ, ∀ i : ℕ, N ≤ i → (n : WithTop ℤ) ≤ ord C P (s i)


def LocalCauchySeqEquivalent {k : Type*} [Field k]
    {C : FunctionFieldCurve k} {P : C.Place}
    (s t : LocalCauchySeq C P) : Prop :=
  LocalSeqTendsToZero (C := C) (P := P) (fun i => s.seq i - t.seq i)

end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_riemann_roch_22_21

end
