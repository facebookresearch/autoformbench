/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib




























open Filter
open scoped Asymptotics

namespace Autoform_Introduction_to_the_Theory_of_Computation_computation_NL_subset_SPACE_logSquared

universe u


abbrev Word (α : Type u) := List α


abbrev Language (α : Type u) := Set (Word α)


abbrev ComplexityClass (α : Type u) := Set (Language α)






inductive Move where
  | left
  | stay
  | right
deriving DecidableEq, Repr








structure StepChoice (State WorkSym : Type) where
  nextState : State
  write : WorkSym
  inputMove : Move
  workMove : Move
deriving DecidableEq, Repr









structure ReadOnlyInputNTM (α : Type u) [Fintype α] where
  State : Type
  WorkSym : Type

  stateFintype : Fintype State
  workFintype : Fintype WorkSym
  stateDecEq : DecidableEq State
  workDecEq : DecidableEq WorkSym

  blank : WorkSym
  start : State
  accept : State
  reject : State
  accept_ne_reject : accept ≠ reject

  step :
    State → Option α → WorkSym →
      Finset (StepChoice State WorkSym)

  step_total :
    ∀ q a γ, q ≠ accept → q ≠ reject →
      (step q a γ).Nonempty








structure Config {α : Type u} [Fintype α] (M : ReadOnlyInputNTM α) where
  state : M.State
  inputHead : Nat
  workHead : Nat
  workTape : Nat → M.WorkSym


def inputSymbol {α : Type u} (w : Word α) (p : Nat) : Option α :=
  w[p]?





def moveInputHead (n p : Nat) : Move → Nat
  | Move.left => p.pred
  | Move.stay => p
  | Move.right => Nat.min (p + 1) n


def moveWorkHead (p : Nat) : Move → Nat
  | Move.left => p.pred
  | Move.stay => p
  | Move.right => p + 1


def IsHalting {α : Type u} [Fintype α]
    (M : ReadOnlyInputNTM α) (q : M.State) : Prop :=
  q = M.accept ∨ q = M.reject


def initialConfig {α : Type u} [Fintype α]
    (M : ReadOnlyInputNTM α) : Config M where
  state := M.start
  inputHead := 0
  workHead := 0
  workTape := fun _ => M.blank


def applyChoice {α : Type u} [Fintype α]
    (M : ReadOnlyInputNTM α) (w : Word α)
    (c : Config M) (ch : StepChoice M.State M.WorkSym) : Config M where
  state := ch.nextState
  inputHead := moveInputHead w.length c.inputHead ch.inputMove
  workHead := moveWorkHead c.workHead ch.workMove
  workTape := fun i =>
    if i = c.workHead then ch.write else c.workTape i





def Next {α : Type u} [Fintype α]
    (M : ReadOnlyInputNTM α) (w : Word α)
    (c c' : Config M) : Prop :=
  (IsHalting M c.state ∧ c' = c) ∨
    (¬ IsHalting M c.state ∧
      ∃ ch : StepChoice M.State M.WorkSym,
        ch ∈ M.step c.state (inputSymbol w c.inputHead)
          (c.workTape c.workHead) ∧
        c' = applyChoice M w c ch)





inductive ReachesIn {α : Type u} [Fintype α]
    (M : ReadOnlyInputNTM α) (w : Word α) :
    Nat → Config M → Config M → Prop where
  | zero (c : Config M) :
      ReachesIn M w 0 c c
  | succ {k : Nat} {c₀ c₁ c₂ : Config M} :
      Next M w c₀ c₁ →
      ReachesIn M w k c₁ c₂ →
      ReachesIn M w (k + 1) c₀ c₂


def IsDeterministic {α : Type u} [Fintype α]
    (M : ReadOnlyInputNTM α) : Prop :=
  ∀ q a γ, (M.step q a γ).card ≤ 1





def ConfigUsesSpace {α : Type u} [Fintype α]
    (M : ReadOnlyInputNTM α) (c : Config M) (s : Nat) : Prop :=
  c.workHead < s ∧ ∀ i, s ≤ i → c.workTape i = M.blank








def DecidesInTime {α : Type u} [Fintype α]
    (M : ReadOnlyInputNTM α) (A : Language α) (T : Nat → Nat) : Prop :=
  ∀ w : Word α,
    (∀ c : Config M,
      ReachesIn M w (T w.length) (initialConfig M) c →
        IsHalting M c.state) ∧
    (w ∈ A ↔
      ∃ c : Config M,
        ReachesIn M w (T w.length) (initialConfig M) c ∧
          c.state = M.accept)







def DecidesInSpace {α : Type u} [Fintype α]
    (M : ReadOnlyInputNTM α) (A : Language α) (S : Nat → Nat) : Prop :=
  ∀ w : Word α, ∃ T : Nat,
    (∀ k : Nat, k ≤ T → ∀ c : Config M,
      ReachesIn M w k (initialConfig M) c →
        ConfigUsesSpace M c (S w.length)) ∧
    (∀ c : Config M,
      ReachesIn M w T (initialConfig M) c →
        IsHalting M c.state) ∧
    (w ∈ A ↔
      ∃ c : Config M,
        ReachesIn M w T (initialConfig M) c ∧
          c.state = M.accept)





def IsBigONat (f g : Nat → Nat) : Prop :=
  (fun n : Nat => (f n : ℝ)) =O[Filter.atTop]
    (fun n : Nat => (g n : ℝ))


def PolynomiallyBounded (T : Nat → Nat) : Prop :=
  ∃ k : Nat, IsBigONat T (fun n => n ^ k)








def logBound (n : Nat) : Nat :=
  Nat.log 2 (n + 2)


def logSquaredBound (n : Nat) : Nat :=
  (logBound n) ^ 2






def P {α : Type u} [Fintype α] : ComplexityClass α :=
  { A : Language α |
    ∃ (M : ReadOnlyInputNTM α) (T : Nat → Nat),
      IsDeterministic M ∧
      PolynomiallyBounded T ∧
      DecidesInTime M A T }





def SPACE {α : Type u} [Fintype α]
    (f : Nat → Nat) : ComplexityClass α :=
  { A : Language α |
    ∃ (M : ReadOnlyInputNTM α) (S : Nat → Nat),
      IsDeterministic M ∧
      IsBigONat S f ∧
      DecidesInSpace M A S }





def NSPACE {α : Type u} [Fintype α]
    (f : Nat → Nat) : ComplexityClass α :=
  { A : Language α |
    ∃ (M : ReadOnlyInputNTM α) (S : Nat → Nat),
      IsBigONat S f ∧
      DecidesInSpace M A S }


def L {α : Type u} [Fintype α] : ComplexityClass α :=
  SPACE (α := α) logBound


def NL {α : Type u} [Fintype α] : ComplexityClass α :=
  NSPACE (α := α) logBound





end Autoform_Introduction_to_the_Theory_of_Computation_computation_NL_subset_SPACE_logSquared
