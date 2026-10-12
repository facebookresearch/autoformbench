/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Autoform_Stacks_Project_stacks_lemma_034H


structure FibredFunctor
    {C : Type u₁} {S : Type u₂} {S' : Type u₃}
    [Category.{v₁} C] [Category.{v₂} S] [Category.{v₃} S']
    (p : S ⥤ C) (p' : S' ⥤ C) where
  toFunctor : S ⥤ S'
  over_p : toFunctor ⋙ p' = p
  preservesStronglyCartesian :
    ∀ ⦃R T : C⦄ ⦃X Y : S⦄ ⦃f : R ⟶ T⦄ ⦃φ : X ⟶ Y⦄,
      p.IsStronglyCartesian f φ →
        p'.IsStronglyCartesian f (toFunctor.map φ)


structure EquivalenceOver
    {C : Type u₁} {A : Type u₂} {B : Type u₃}
    [Category.{v₁} C] [Category.{v₂} A] [Category.{v₃} B]
    (pA : A ⥤ C) (pB : B ⥤ C) where
  toEquivalence : A ≌ B
  overFunctor : toEquivalence.functor ⋙ pB ≅ pA
  overInverse : toEquivalence.inverse ⋙ pA ≅ pB


variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {S' : Type u₃} [Category.{v₃} S']
variable {p : S ⥤ C} {p' : S' ⥤ C}
variable (F : FibredFunctor p p')


structure RelativeInertiaObj where
  x : S
  a : x ≅ x
  F_a_id : F.toFunctor.map a.hom = 𝟙 (F.toFunctor.obj x)


structure RelativeInertiaHom (X Y : RelativeInertiaObj F) where
  hom : X.x ⟶ Y.x
  comm : X.a.hom ≫ hom = hom ≫ Y.a.hom

instance relativeInertiaCategory : Category (RelativeInertiaObj F) where
  Hom X Y := RelativeInertiaHom F X Y
  id X := {
    hom := 𝟙 X.x
    comm := by simp
  }
  comp := by
    intro X Y Z f g
    exact {
      hom := f.hom ≫ g.hom
      comm := by
        calc
          X.a.hom ≫ (f.hom ≫ g.hom) = (X.a.hom ≫ f.hom) ≫ g.hom := by
            simp [Category.assoc]
          _ = (f.hom ≫ Y.a.hom) ≫ g.hom := by
            rw [f.comm]
          _ = f.hom ≫ (Y.a.hom ≫ g.hom) := by
            simp [Category.assoc]
          _ = f.hom ≫ (g.hom ≫ Z.a.hom) := by
            rw [g.comm]
          _ = (f.hom ≫ g.hom) ≫ Z.a.hom := by
            simp [Category.assoc]
    }


def relativeInertiaProjection : RelativeInertiaObj F ⥤ C where
  obj X := p.obj X.x
  map f := p.map f.hom
  map_id X := by
    change p.map (𝟙 X.x) = 𝟙 (p.obj X.x)
    simp
  map_comp f g := by
    change p.map (f.hom ≫ g.hom) = p.map f.hom ≫ p.map g.hom
    simp



variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {S' : Type u₃} [Category.{v₃} S']
variable {p : S ⥤ C} {p' : S' ⥤ C}
variable (F : FibredFunctor p p')






structure DiagonalTwoFiberProductObj where
  x : S
  y : S
  iota : x ≅ y
  kappa : x ≅ y
  F_eq : F.toFunctor.map iota.hom = F.toFunctor.map kappa.hom


structure DiagonalTwoFiberProductHom
    (X Y : DiagonalTwoFiberProductObj F) where
  left : X.x ⟶ Y.x
  right : X.y ⟶ Y.y
  iota_comm : X.iota.hom ≫ right = left ≫ Y.iota.hom
  kappa_comm : X.kappa.hom ≫ right = left ≫ Y.kappa.hom

instance diagonalTwoFiberProductCategory :
    Category (DiagonalTwoFiberProductObj F) where
  Hom X Y := DiagonalTwoFiberProductHom F X Y
  id X := {
    left := 𝟙 X.x
    right := 𝟙 X.y
    iota_comm := by simp
    kappa_comm := by simp
  }
  comp := by
    intro X Y Z f g
    exact {
      left := f.left ≫ g.left
      right := f.right ≫ g.right
      iota_comm := by
        calc
          X.iota.hom ≫ (f.right ≫ g.right) = (X.iota.hom ≫ f.right) ≫ g.right := by
            simp [Category.assoc]
          _ = (f.left ≫ Y.iota.hom) ≫ g.right := by
            rw [f.iota_comm]
          _ = f.left ≫ (Y.iota.hom ≫ g.right) := by
            simp [Category.assoc]
          _ = f.left ≫ (g.left ≫ Z.iota.hom) := by
            rw [g.iota_comm]
          _ = (f.left ≫ g.left) ≫ Z.iota.hom := by
            simp [Category.assoc]
      kappa_comm := by
        calc
          X.kappa.hom ≫ (f.right ≫ g.right) = (X.kappa.hom ≫ f.right) ≫ g.right := by
            simp [Category.assoc]
          _ = (f.left ≫ Y.kappa.hom) ≫ g.right := by
            rw [f.kappa_comm]
          _ = f.left ≫ (Y.kappa.hom ≫ g.right) := by
            simp [Category.assoc]
          _ = f.left ≫ (g.left ≫ Z.kappa.hom) := by
            rw [g.kappa_comm]
          _ = (f.left ≫ g.left) ≫ Z.kappa.hom := by
            simp [Category.assoc]
    }


def diagonalTwoFiberProductProjection :
    DiagonalTwoFiberProductObj F ⥤ C where
  obj X := p.obj X.x
  map f := p.map f.left
  map_id X := by
    change p.map (𝟙 X.x) = 𝟙 (p.obj X.x)
    simp
  map_comp f g := by
    change p.map (f.left ≫ g.left) = p.map f.left ≫ p.map g.left
    simp




end Autoform_Stacks_Project_stacks_lemma_034H
