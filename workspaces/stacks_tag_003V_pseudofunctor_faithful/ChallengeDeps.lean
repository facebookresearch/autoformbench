import Mathlib

open CategoryTheory
open Bicategory

namespace Autoform_Stacks_Project_stacks_tag_003V_pseudofunctor_faithful

universe v₁ v₂ u₁ u₂


def HasLifts {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S] (p : S ⥤ C) : Prop :=
  ∀ (x : S) (V : C) (f : V ⟶ p.obj x),
    ∃ (y : S) (φ : y ⟶ x), p.IsHomLift f φ


def UniqueLiftsForTriangles {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S] (p : S ⥤ C) : Prop :=
  ∀ (x y z : S) (φ : y ⟶ x) (ψ : z ⟶ x) (f : p.obj z ⟶ p.obj y),
    f ≫ p.map φ = p.map ψ →
      ∃! (χ : z ⟶ y), p.map χ = f ∧ χ ≫ φ = ψ


def IsFibredInGroupoids {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S] (p : S ⥤ C) : Prop :=
  HasLifts p ∧ UniqueLiftsForTriangles p


def FibersAreGroupoids {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S] (p : S ⥤ C) : Prop :=
  ∀ (U : C) {x y : p.Fiber U} (f : x ⟶ y), IsIso f


def ValuesInGroupoids {C : Type u₁} [Category.{v₁} C]
    (P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat) : Prop :=
  ∀ (U : C) {x y : P.obj (LocallyDiscrete.mk (Opposite.op U))} (f : x ⟶ y), IsIso f






structure ChoiceOfPullbacks
    {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C) where
  obj :
    ∀ {U V : C}, (f : U ⟶ V) → p.Fiber V → p.Fiber U
  hom :
    ∀ {U V : C} (f : U ⟶ V) (a : p.Fiber V),
      (obj f a).1 ⟶ a.1
  overBase :
    ∀ {U V : C} (f : U ⟶ V) (a : p.Fiber V),
      p.map (hom f a) = eqToHom ((obj f a).2) ≫ f ≫ eqToHom (a.2.symm)
  stronglyCartesian :
    ∀ {U V : C} (f : U ⟶ V) (a : p.Fiber V),
      p.IsStronglyCartesian f (hom f a)





structure PullbackFunctorFamilyFromChoice
    {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C)
    (cp : ChoiceOfPullbacks p) where
  pull :
    ∀ {U V : C}, (f : U ⟶ V) → p.Fiber V ⥤ p.Fiber U
  obj_eq :
    ∀ {U V : C} (f : U ⟶ V) (a : p.Fiber V),
      (pull f).obj a = cp.obj f a
  map_comm :
    ∀ {U V : C} (f : U ⟶ V) {a b : p.Fiber V} (φ : a ⟶ b),
      Functor.Fiber.fiberInclusion.map ((eqToIso (obj_eq f a)).hom) ≫
          cp.hom f a ≫
          Functor.Fiber.fiberInclusion.map φ =
        Functor.Fiber.fiberInclusion.map ((pull f).map φ) ≫
          Functor.Fiber.fiberInclusion.map ((eqToIso (obj_eq f b)).hom) ≫
          cp.hom f b





structure PseudofunctorDataFromChoiceOfPullbacks
    {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C)
    (cp : ChoiceOfPullbacks p) where
  family : PullbackFunctorFamilyFromChoice p cp
  alphaComp :
    ∀ {U V W : C} (f : U ⟶ V) (g : V ⟶ W),
      family.pull (f ≫ g) ≅ family.pull g ⋙ family.pull f
  alphaId :
    ∀ (U : C), family.pull (𝟙 U) ≅ 𝟭 (p.Fiber U)
  P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat
  obj_eq :
    ∀ U : C,
      P.obj (LocallyDiscrete.mk (Opposite.op U)) = Cat.of (p.Fiber U)
  map_eq :
    ∀ {U V : C} (f : U ⟶ V),
      HEq (P.map (f.op.toLoc)).toFunctor (family.pull f)
  mapComp_eq :
    ∀ {U V W : C} (f : U ⟶ V) (g : V ⟶ W),
      HEq (P.mapComp (g.op.toLoc) (f.op.toLoc))
        (CategoryTheory.Cat.Hom.isoMk (alphaComp f g))
  mapId_eq :
    ∀ U : C,
      HEq (P.mapId (LocallyDiscrete.mk (Opposite.op U)))
        (CategoryTheory.Cat.Hom.isoMk (alphaId U))
  valuesInGroupoids : ValuesInGroupoids P







end Autoform_Stacks_Project_stacks_tag_003V_pseudofunctor_faithful
