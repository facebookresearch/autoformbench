/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory
open Bicategory
open Pseudofunctor

universe uC vC uS vS uT vT uF vF

namespace Autoform_Stacks_Project_stacks_lemma_fibred_strict



structure FibredOverFunctor {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    {T : Type uT} [Category.{vT} T]
    (p : S ⥤ C) (q : T ⥤ C) where
  toFunctor : S ⥤ T
  overBase : toFunctor ⋙ q = p
  map_isStronglyCartesian :
    ∀ ⦃R S' : C⦄ ⦃a b : S⦄ ⦃f : R ⟶ S'⦄ ⦃φ : a ⟶ b⦄,
      p.IsStronglyCartesian f φ →
        q.IsStronglyCartesian f (toFunctor.map φ)

namespace FibredOverFunctor

def id {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S] (p : S ⥤ C) :
    FibredOverFunctor p p :=
  ⟨𝟭 S, by simpa using Functor.id_comp p,
    by
      intro R S' a b f φ hφ
      simpa using hφ⟩

def comp {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    {T : Type uT} [Category.{vT} T]
    {U : Type uF} [Category.{vF} U]
    {p : S ⥤ C} {q : T ⥤ C} {r : U ⥤ C}
    (F : FibredOverFunctor p q) (G : FibredOverFunctor q r) :
    FibredOverFunctor p r :=
  ⟨F.toFunctor ⋙ G.toFunctor,
    by
      calc
        (F.toFunctor ⋙ G.toFunctor) ⋙ r = F.toFunctor ⋙ q := by
          simpa [Functor.assoc] using congrArg (fun H => F.toFunctor ⋙ H) G.overBase
        _ = p := F.overBase,
    by
      intro R S' a b f φ hφ
      exact G.map_isStronglyCartesian (F.map_isStronglyCartesian hφ)⟩

end FibredOverFunctor


structure OverNatIso {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    {T : Type uT} [Category.{vT} T]
    {p : S ⥤ C} {q : T ⥤ C}
    (F G : FibredOverFunctor p q) where
  iso : F.toFunctor ≅ G.toFunctor
  overBase : ∀ x : S,
    let hF : q.obj (F.toFunctor.obj x) = p.obj x := by
      simpa using congrArg (fun H => H.obj x) F.overBase
    let hG : q.obj (G.toFunctor.obj x) = p.obj x := by
      simpa using congrArg (fun H => H.obj x) G.overBase
    q.map (iso.hom.app x) = eqToHom hF ≫ eqToHom hG.symm


structure EquivalenceOver {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    {T : Type uT} [Category.{vT} T]
    (p : S ⥤ C) (q : T ⥤ C) where
  G : FibredOverFunctor p q
  F : FibredOverFunctor q p
  equiv :
    Nonempty (OverNatIso (FibredOverFunctor.comp G F) (FibredOverFunctor.id p)) ∧
    Nonempty (OverNatIso (FibredOverFunctor.comp F G) (FibredOverFunctor.id q))



end Autoform_Stacks_Project_stacks_lemma_fibred_strict
