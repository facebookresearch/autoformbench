import Mathlib

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

namespace Autoform_Stacks_Project_stacks_isEquivalenceIn2Category_of_isEquivalence_003Z

def HasLifts {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S] (p : S ⥤ C) : Prop :=
  ∀ (x : S) (V : C) (f : V ⟶ p.obj x),
    ∃ (y : S) (h : p.obj y = V) (φ : y ⟶ x),
      p.map φ = eqToHom h ≫ f

def UniqueLiftsForTriangles {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S] (p : S ⥤ C) : Prop :=
  ∀ (x y z : S) (φ : y ⟶ x) (ψ : z ⟶ x) (f : p.obj z ⟶ p.obj y),
    f ≫ p.map φ = p.map ψ →
      ∃! (χ : z ⟶ y), p.map χ = f ∧ χ ≫ φ = ψ

def IsFibredInGroupoids {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S] (p : S ⥤ C) : Prop :=
  HasLifts p ∧ UniqueLiftsForTriangles p

structure OverFunctor {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S]
    {S' : Type u₂} [Category.{v₂} S']
    (p : S ⥤ C) (p' : S' ⥤ C) where
  toFunctor : S ⥤ S'
  overBase : toFunctor ⋙ p' = p

namespace OverFunctor

def id {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S] (p : S ⥤ C) :
    OverFunctor p p :=
  ⟨𝟭 S, by simpa using Functor.id_comp p⟩

def comp {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S]
    {S' : Type u₂} [Category.{v₂} S']
    {S'' : Type u₂} [Category.{v₂} S'']
    {p : S ⥤ C} {p' : S' ⥤ C} {p'' : S'' ⥤ C}
    (F : OverFunctor p p') (G : OverFunctor p' p'') :
    OverFunctor p p'' :=
  ⟨F.toFunctor ⋙ G.toFunctor,
    by rw [Functor.assoc, G.overBase, F.overBase]⟩

def onFiber {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S]
    {S' : Type u₂} [Category.{v₂} S']
    {p : S ⥤ C} {p' : S' ⥤ C}
    (G : OverFunctor p p') (U : C) :
    p.Fiber U ⥤ p'.Fiber U :=
  Functor.Fiber.inducedFunctor
    (p := p')
    (S := U)
    (F := Functor.Fiber.fiberInclusion ⋙ G.toFunctor)
    (by
      rw [Functor.assoc, G.overBase]
      exact Fiber.fiberInclusion_comp_eq_const)

end OverFunctor

structure OverNatIso {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S]
    {S' : Type u₂} [Category.{v₂} S']
    {p : S ⥤ C} {p' : S' ⥤ C}
    (F G : OverFunctor p p') where
  iso : F.toFunctor ≅ G.toFunctor
  overBase : ∀ x : S,
    let hF : p'.obj (F.toFunctor.obj x) = p.obj x := by
      simpa using congrArg (fun H => H.obj x) F.overBase
    let hG : p'.obj (G.toFunctor.obj x) = p.obj x := by
      simpa using congrArg (fun H => H.obj x) G.overBase
    p'.map (iso.hom.app x) = eqToHom hF ≫ eqToHom hG.symm

def IsEquivalenceOver {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S]
    {S' : Type u₂} [Category.{v₂} S']
    {p : S ⥤ C} {p' : S' ⥤ C}
    (G : OverFunctor p p') : Prop :=
  ∃ F : OverFunctor p' p,
    Nonempty (OverNatIso (OverFunctor.comp G F) (OverFunctor.id p)) ∧
    Nonempty (OverNatIso (OverFunctor.comp F G) (OverFunctor.id p'))

section

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {S' : Type u₂} [Category.{v₂} S']
variable {p : S ⥤ C} {p' : S' ⥤ C}
variable (G : OverFunctor p p')









end

end Autoform_Stacks_Project_stacks_isEquivalenceIn2Category_of_isEquivalence_003Z
