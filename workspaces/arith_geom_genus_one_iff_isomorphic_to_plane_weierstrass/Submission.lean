import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_genus_one_iff_isomorphic_to_plane_weierstrass

noncomputable section

open scoped BigOperators

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_genus_one_iff_isomorphic_to_plane_weierstrass


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
  add_mem' := fun {x y} hx hy => ring_add_mem v x y hx hy
  neg_mem' := by
    intro x hx
    simpa [map_neg v x] using hx
  mul_mem' := fun {x y} hx hy => ring_mul_mem v x y hx hy

end NormalizedDiscreteValuation


theorem maximalIdeal_add_mem {F : Type*} [Field F] (v : NormalizedDiscreteValuation F)
    (x y : v.ring) (hx : (0 : WithTop ℤ) < v x.1) (hy : (0 : WithTop ℤ) < v y.1) :
    (0 : WithTop ℤ) < v (x + y).1 := by
  sorry


theorem maximalIdeal_smul_mem {F : Type*} [Field F] (v : NormalizedDiscreteValuation F)
    (a : v.ring) (x : v.ring) (hx : (0 : WithTop ℤ) < v x.1) :
    (0 : WithTop ℤ) < v (a • x).1 := by
  sorry

namespace NormalizedDiscreteValuation

variable {F : Type*} [Field F] (v : NormalizedDiscreteValuation F)


def maximalIdeal : Ideal v.ring where
  carrier := { x : v.ring | (0 : WithTop ℤ) < v x.1 }
  zero_mem' := by
    simp
  add_mem' := fun {x y} hx hy => maximalIdeal_add_mem v x y hx hy
  smul_mem' := fun a {x} hx => maximalIdeal_smul_mem v a x hx

end NormalizedDiscreteValuation


theorem maximalIdeal_isMaximal {F : Type*} [Field F] (v : NormalizedDiscreteValuation F) :
    v.maximalIdeal.IsMaximal := by
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

noncomputable instance instResidueFieldField {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) : Field (C.ResidueField P) :=
  NormalizedDiscreteValuation.residueFieldField (C.placeValuation P)

noncomputable instance instResidueFieldAlgebra {k : Type*} [Field k]
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
  add_mem' := fun {f g} hf hg => riemannRochSpace_add_mem C D f g hf hg
  smul_mem' := fun c {f} hf => riemannRochSpace_smul_mem C D c f hf


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


def HasGenusOne {k : Type*} [Field k] (C : FunctionFieldCurve k) : Prop :=
  IsGenus C 1


def HasRationalPoint {k : Type*} [Field k] (C : FunctionFieldCurve k) : Prop :=
  ∃ P : C.Place, C.residueDegree P = 1












theorem genus_one_iff_isomorphic_to_plane_weierstrass
    {k : Type*} [Field k] [PerfectField k]
    (C : FunctionFieldCurve k)
    (hCk : HasRationalPoint C) :
    HasGenusOne C ↔ IsIsomorphicToPlaneWeierstrassCurve C := by
  sorry

end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_genus_one_iff_isomorphic_to_plane_weierstrass

end
