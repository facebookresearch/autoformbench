/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


























noncomputable section

universe u

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_weil_chatelet_group_iso_H1_postDescent









structure ContinuousAdditiveGaloisModule
    (Γ A : Type u) [Group Γ] [TopologicalSpace Γ] [AddCommGroup A] [TopologicalSpace A] where
  discrete : DiscreteTopology A
  gamma_mul_continuous : Continuous (fun p : Γ × Γ => p.1 * p.2)
  gamma_inv_continuous : Continuous (fun γ : Γ => γ⁻¹)
  act : Γ → A → A
  act_zero : ∀ γ : Γ, act γ 0 = 0
  act_add : ∀ (γ : Γ) (a b : A), act γ (a + b) = act γ a + act γ b
  act_one : ∀ a : A, act 1 a = a
  act_mul : ∀ (γ δ : Γ) (a : A), act (γ * δ) a = act γ (act δ a)
  act_continuous : ∀ a : A, Continuous (fun γ : Γ => act γ a)

variable {Γ A : Type u} [Group Γ] [TopologicalSpace Γ] [AddCommGroup A] [TopologicalSpace A]


structure OneCocycle (M : ContinuousAdditiveGaloisModule Γ A) where
  toFun : Γ → A
  continuous' : Continuous toFun
  cocycle' : ∀ γ δ : Γ, toFun (γ * δ) = toFun γ + M.act γ (toFun δ)

instance instCoeFunOneCocycle (M : ContinuousAdditiveGaloisModule Γ A) :
    CoeFun (OneCocycle M) (fun _ => Γ → A) where
  coe z := z.toFun










def Cohomologous
    (M : ContinuousAdditiveGaloisModule Γ A) (z w : OneCocycle M) : Prop :=
  ∃ a : A, ∀ γ : Γ, w γ = z γ + M.act γ a - a


















structure ContinuousGaloisTorsor (M : ContinuousAdditiveGaloisModule Γ A) where
  Carrier : Type u
  [carrierTopology : TopologicalSpace Carrier]
  [carrierDiscrete : DiscreteTopology Carrier]
  nonempty : Nonempty Carrier
  vadd : A → Carrier → Carrier
  gal : Γ → Carrier → Carrier
  vadd_zero : ∀ t : Carrier, vadd 0 t = t
  vadd_add : ∀ (a b : A) (t : Carrier), vadd (a + b) t = vadd a (vadd b t)
  vadd_free : ∀ {a b : A} {t : Carrier}, vadd a t = vadd b t → a = b
  vadd_transitive : ∀ t u : Carrier, ∃ a : A, vadd a t = u
  gal_one : ∀ t : Carrier, gal 1 t = t
  gal_mul : ∀ (γ δ : Γ) (t : Carrier), gal (γ * δ) t = gal γ (gal δ t)
  gal_vadd : ∀ (γ : Γ) (a : A) (t : Carrier),
    gal γ (vadd a t) = vadd (M.act γ a) (gal γ t)
  gal_continuous : ∀ t : Carrier, Continuous (fun γ : Γ => gal γ t)

attribute [instance] ContinuousGaloisTorsor.carrierTopology
attribute [instance] ContinuousGaloisTorsor.carrierDiscrete


def ContinuousTorsorIso
    (M : ContinuousAdditiveGaloisModule Γ A)
    (X Y : ContinuousGaloisTorsor M) : Prop :=
  ∃ f : X.Carrier → Y.Carrier,
    ∃ g : Y.Carrier → X.Carrier,
      Continuous f ∧
        Continuous g ∧
          (∀ t : X.Carrier, g (f t) = t) ∧
            (∀ t : Y.Carrier, f (g t) = t) ∧
              (∀ (a : A) (t : X.Carrier), f (X.vadd a t) = Y.vadd a (f t)) ∧
                (∀ (γ : Γ) (t : X.Carrier), f (X.gal γ t) = Y.gal γ (f t))


















def IsBaerSum
    (M : ContinuousAdditiveGaloisModule Γ A)
    (X Y Z : ContinuousGaloisTorsor M) : Prop :=
  ∃ q : X.Carrier → Y.Carrier → Z.Carrier,
    (∀ (x1 x2 : X.Carrier) (y1 y2 : Y.Carrier),
      q x1 y1 = q x2 y2 ↔
        ∃ a : A, x2 = X.vadd a x1 ∧ y2 = Y.vadd (-a) y1) ∧
      (∀ z : Z.Carrier, ∃ x : X.Carrier, ∃ y : Y.Carrier, q x y = z) ∧
        (∀ (a : A) (x : X.Carrier) (y : Y.Carrier),
          Z.vadd a (q x y) = q (X.vadd a x) y) ∧
          (∀ (γ : Γ) (x : X.Carrier) (y : Y.Carrier),
            Z.gal γ (q x y) = q (X.gal γ x) (Y.gal γ y)) ∧
            (∀ y : Y.Carrier, Continuous (fun x : X.Carrier => q x y)) ∧
              (∀ x : X.Carrier, Continuous (fun y : Y.Carrier => q x y))






def AddCommGroupRealizes
    {X : Type*} (G : AddCommGroup X) (zero : X) (addRel : X → X → X → Prop) :
    Prop :=
  letI : AddCommGroup X := G
  (0 : X) = zero ∧
    ∀ x y z : X, addRel x y z ↔ x + y = z



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_weil_chatelet_group_iso_H1_postDescent

end