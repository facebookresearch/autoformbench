/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
























universe u v w

namespace Autoform_Noncommutative_Algebra_noncomm_alg_remark_7_1_graded_projective_cover







def IsIdempotentElement {A : Type u} [Mul A] (e : A) : Prop :=
  e * e = e







abbrev IsLeftArtinianRing (A : Type u) [Ring A] : Prop :=
  IsArtinian A A








structure NonnegativelyGradedRing (R : Type u) [Ring R] where
  grade : ℕ → AddSubgroup R
  [decomposition : DirectSum.Decomposition grade]
  one_mem : (1 : R) ∈ grade 0
  mul_mem :
    ∀ ⦃i j : ℕ⦄ {x y : R},
      x ∈ grade i → y ∈ grade j → x * y ∈ grade (i + j)

attribute [instance] NonnegativelyGradedRing.decomposition

namespace NonnegativelyGradedRing




def degreeZeroSubring
    {R : Type u} [Ring R]
    (G : NonnegativelyGradedRing R) :
    Subring R where
  carrier := G.grade 0
  zero_mem' := (G.grade 0).zero_mem
  one_mem' := G.one_mem
  add_mem' := by
    intro x y hx hy
    exact (G.grade 0).add_mem hx hy
  mul_mem' := by
    intro x y hx hy
    simpa using G.mul_mem (i := 0) (j := 0) hx hy
  neg_mem' := by
    intro x hx
    exact (G.grade 0).neg_mem hx





def gradeAtInt
    {R : Type u} [Ring R]
    (G : NonnegativelyGradedRing R)
    (n : ℤ) :
    AddSubgroup R :=
  if 0 ≤ n then G.grade (Int.toNat n) else ⊥

end NonnegativelyGradedRing








structure ZGradedModule
    {R : Type u} [Ring R]
    (G : NonnegativelyGradedRing R)
    (M : Type v) [AddCommGroup M] [Module R M] where
  grade : ℤ → AddSubgroup M
  [decomposition : DirectSum.Decomposition grade]
  smul_mem :
    ∀ ⦃i : ℕ⦄ ⦃j : ℤ⦄ {r : R} {m : M},
      r ∈ G.grade i → m ∈ grade j → r • m ∈ grade ((i : ℤ) + j)

attribute [instance] ZGradedModule.decomposition




def IsHomogeneousLinearMap
    {R : Type u} [Ring R]
    {G : NonnegativelyGradedRing R}
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (GM : ZGradedModule G M)
    (GN : ZGradedModule G N)
    (f : M →ₗ[R] N) : Prop :=
  ∀ n : ℤ, ∀ ⦃m : M⦄, m ∈ GM.grade n → f m ∈ GN.grade n





def IsGradedSubmodule
    {R : Type u} [Ring R]
    {G : NonnegativelyGradedRing R}
    {M : Type v} [AddCommGroup M] [Module R M]
    (GM : ZGradedModule G M)
    (N : Submodule R M) : Prop :=
  DirectSum.SetLike.IsHomogeneous GM.grade N





def ConcentratedInDegree
    {R : Type u} [Ring R]
    {G : NonnegativelyGradedRing R}
    {M : Type v} [AddCommGroup M] [Module R M]
    (GM : ZGradedModule G M)
    (d : ℤ) : Prop :=
  ∀ n : ℤ, n ≠ d → GM.grade n = ⊥





def IsGradedSimpleModule
    {R : Type u} [Ring R]
    {G : NonnegativelyGradedRing R}
    {M : Type v} [AddCommGroup M] [Module R M]
    (GM : ZGradedModule G M) : Prop :=
  Nontrivial M ∧
    ∀ N : Submodule R M,
      IsGradedSubmodule GM N → N ≠ ⊥ → N = ⊤






def IsEssentialSurjection
    {A : Type u} [Ring A]
    {P : Type v} [AddCommGroup P] [Module A P]
    {M : Type w} [AddCommGroup M] [Module A M]
    (f : P →ₗ[A] M) : Prop :=
  Function.Surjective f ∧
    ∀ N : Submodule A P,
      N ≠ ⊤ → ¬ Function.Surjective (f.comp N.subtype)




structure ProjectiveCoverFrom
    (A : Type u) [Ring A]
    (P : Type v) [AddCommGroup P] [Module A P]
    (M : Type w) [AddCommGroup M] [Module A M] where
  projective : Module.Projective A P
  coverMap : P →ₗ[A] M
  essential : IsEssentialSurjection coverMap








def GradedProjective
    {R : Type u} [Ring R]
    {G : NonnegativelyGradedRing R}
    {P : Type v} [AddCommGroup P] [Module R P]
    (GP : ZGradedModule G P) : Prop :=
  ∀ {M N : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N],
      ∀ (GM : ZGradedModule G M)
        (GN : ZGradedModule G N)
        (f : M →ₗ[R] N),
        IsHomogeneousLinearMap GM GN f →
        Function.Surjective f →
        ∀ (g : P →ₗ[R] N),
          IsHomogeneousLinearMap GP GN g →
          ∃ lift : P →ₗ[R] M,
            IsHomogeneousLinearMap GP GM lift ∧ f.comp lift = g





def IsGradedEssentialSurjection
    {R : Type u} [Ring R]
    {G : NonnegativelyGradedRing R}
    {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M]
    (GP : ZGradedModule G P)
    (GM : ZGradedModule G M)
    (f : P →ₗ[R] M) : Prop :=
  IsHomogeneousLinearMap GP GM f ∧
    Function.Surjective f ∧
      ∀ N : Submodule R P,
        IsGradedSubmodule GP N →
          N ≠ ⊤ → ¬ Function.Surjective (f.comp N.subtype)





structure GradedProjectiveCoverFrom
    {R : Type u} [Ring R]
    {G : NonnegativelyGradedRing R}
    {P : Type v} [AddCommGroup P] [Module R P]
    (GP : ZGradedModule G P)
    {M : Type w} [AddCommGroup M] [Module R M]
    (GM : ZGradedModule G M) where
  projective : GradedProjective.{u, v, w} GP
  coverMap : P →ₗ[R] M
  essential : IsGradedEssentialSurjection GP GM coverMap





def principalLeftIdeal (A : Type u) [Ring A] (e : A) : Submodule A A :=
  Submodule.span A ({e} : Set A)







def PrincipalLeftIdealGradingIsInduced
    {R : Type u} [Ring R]
    (G : NonnegativelyGradedRing R)
    (e : R)
    (GP : ZGradedModule G (principalLeftIdeal R e)) : Prop :=
  ∀ n : ℤ, ∀ x : principalLeftIdeal R e,
    x ∈ GP.grade n ↔ (x : R) ∈ G.gradeAtInt n








structure DegreeZeroProjectiveCoverIdempotent
    {R : Type u} [Ring R]
    (G : NonnegativelyGradedRing R)
    {L : Type v} [AddCommGroup L] [Module R L]
    (e₀ : G.degreeZeroSubring) where
  idempotent : IsIdempotentElement e₀
  cover :
    (letI : Module G.degreeZeroSubring L :=
      Module.compHom L (G.degreeZeroSubring).subtype;
    ProjectiveCoverFrom
      G.degreeZeroSubring
      (principalLeftIdeal G.degreeZeroSubring e₀)
      L)








structure GradedProjectiveCoverOnPrincipalLeftIdeal
    {R : Type u} [Ring R]
    (G : NonnegativelyGradedRing R)
    {L : Type v} [AddCommGroup L] [Module R L]
    (GLmod : ZGradedModule G L)
    (e₀ : G.degreeZeroSubring)
    (e₀data : DegreeZeroProjectiveCoverIdempotent G (L := L) e₀) where
  gradedModule :
    ZGradedModule G (principalLeftIdeal R (e₀ : R))
  grading_induced :
    PrincipalLeftIdealGradingIsInduced G (e₀ : R) gradedModule
  gradedCover :
    GradedProjectiveCoverFrom gradedModule GLmod
  extends_degreeZero :
    ∀ (x₀ : principalLeftIdeal G.degreeZeroSubring e₀)
      (x : principalLeftIdeal R (e₀ : R)),
      (x : R) = ((x₀ : G.degreeZeroSubring) : R) →
        gradedCover.coverMap x =
          (letI : Module G.degreeZeroSubring L :=
            Module.compHom L (G.degreeZeroSubring).subtype;
          e₀data.cover.coverMap x₀)



end Autoform_Noncommutative_Algebra_noncomm_alg_remark_7_1_graded_projective_cover
