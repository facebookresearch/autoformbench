/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory

universe uC vC uX vX uY vY uZ vZ

namespace Autoform_Stacks_Project_stacks_lemma_06N7


def HasLifts {C : Type uC} [Category.{vC} C]
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C) : Prop :=
  ∀ (x : S) (V : C) (f : V ⟶ p.obj x),
    ∃ (y : S) (h : p.obj y = V) (φ : y ⟶ x),
      p.map φ = eqToHom h ≫ f


def UniqueLiftsForTriangles {C : Type uC} [Category.{vC} C]
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C) : Prop :=
  ∀ (x y z : S) (φ : y ⟶ x) (ψ : z ⟶ x) (f : p.obj z ⟶ p.obj y),
    f ≫ p.map φ = p.map ψ →
      ∃! (χ : z ⟶ y), p.map χ = f ∧ χ ≫ φ = ψ


def IsFibredInGroupoids {C : Type uC} [Category.{vC} C]
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C) : Prop :=
  HasLifts p ∧ UniqueLiftsForTriangles p


structure OverFunctor {C : Type uC} [Category.{vC} C]
    {S : Type uX} [Category.{vX} S]
    {T : Type uY} [Category.{vY} T]
    (p : S ⥤ C) (q : T ⥤ C) where
  toFunctor : S ⥤ T
  overBase : toFunctor ⋙ q = p

namespace OverFunctor


def id {C : Type uC} [Category.{vC} C]
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C) :
    OverFunctor p p :=
  ⟨𝟭 S, by simpa using Functor.id_comp p⟩


def comp {C : Type uC} [Category.{vC} C]
    {S : Type uX} [Category.{vX} S]
    {T : Type uY} [Category.{vY} T]
    {U : Type uZ} [Category.{vZ} U]
    {p : S ⥤ C} {q : T ⥤ C} {r : U ⥤ C}
    (F : OverFunctor p q) (G : OverFunctor q r) :
    OverFunctor p r :=
  ⟨F.toFunctor ⋙ G.toFunctor,
    by
      calc
        (F.toFunctor ⋙ G.toFunctor) ⋙ r = F.toFunctor ⋙ q := by
          simpa [Functor.assoc] using congrArg (fun H => F.toFunctor ⋙ H) G.overBase
        _ = p := F.overBase⟩

end OverFunctor


structure OverNatIso {C : Type uC} [Category.{vC} C]
    {S : Type uX} [Category.{vX} S]
    {T : Type uY} [Category.{vY} T]
    {p : S ⥤ C} {q : T ⥤ C}
    (F G : OverFunctor p q) where
  iso : F.toFunctor ≅ G.toFunctor
  overBase : ∀ x : S,
    let hF : q.obj (F.toFunctor.obj x) = p.obj x := by
      simpa using congrArg (fun H => H.obj x) F.overBase
    let hG : q.obj (G.toFunctor.obj x) = p.obj x := by
      simpa using congrArg (fun H => H.obj x) G.overBase
    q.map (iso.hom.app x) = eqToHom hF ≫ eqToHom hG.symm


def IsEquivalenceOver {C : Type uC} [Category.{vC} C]
    {S : Type uX} [Category.{vX} S]
    {T : Type uY} [Category.{vY} T]
    {p : S ⥤ C} {q : T ⥤ C}
    (F : OverFunctor p q) : Prop :=
  ∃ G : OverFunctor q p,
    Nonempty (OverNatIso (OverFunctor.comp F G) (OverFunctor.id p)) ∧
    Nonempty (OverNatIso (OverFunctor.comp G F) (OverFunctor.id q))

section

variable {C : Type uC} [Category.{vC} C]



end

end Autoform_Stacks_Project_stacks_lemma_06N7
