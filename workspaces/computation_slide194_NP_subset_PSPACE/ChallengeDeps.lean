import Mathlib



































open Asymptotics
open Turing

universe u

namespace Autoform_Introduction_to_the_Theory_of_Computation_computation_slide194_NP_subset_PSPACE








def encodeInput {α Γ : Type u} (encodeSym : α → Γ) (w : List α) : List Γ :=
  w.map encodeSym






structure LocatedCfg (Γ Λ : Type u) [Inhabited Γ] where
  cfg : TM0.Cfg Γ Λ
  pos : ℤ

namespace LocatedCfg

variable {Γ Λ : Type u} [Inhabited Γ]


def nextOfStmt (q' : Λ) (stmt : TM0.Stmt Γ)
    (c : LocatedCfg Γ Λ) : LocatedCfg Γ Λ :=
  match stmt with
  | TM0.Stmt.write a =>
      { cfg := { q := q', Tape := c.cfg.Tape.write a }
        pos := c.pos }
  | TM0.Stmt.move Dir.left =>
      { cfg := { q := q', Tape := c.cfg.Tape.move Dir.left }
        pos := c.pos - 1 }
  | TM0.Stmt.move Dir.right =>
      { cfg := { q := q', Tape := c.cfg.Tape.move Dir.right }
        pos := c.pos + 1 }

end LocatedCfg






def HeadWithinSpaceWindow (p : ℤ) (s : ℕ) : Prop :=
  -((s : ℤ)) ≤ p ∧ p ≤ (s : ℤ)
















structure DTM0 (α : Type u) where
  Γ : Type u
  [gammaInhabited : Inhabited Γ]
  [gammaFintype : Fintype Γ]
  [gammaDecEq : DecidableEq Γ]
  encodeSym : α → Γ
  encodeSym_injective : Function.Injective encodeSym
  encodeSym_ne_blank : ∀ a : α, encodeSym a ≠ default
  State : Type u
  [stateInhabited : Inhabited State]
  [stateFintype : Fintype State]
  [stateDecEq : DecidableEq State]
  machine : TM0.Machine Γ State
  accept : State
  reject : State
  accept_ne_reject : accept ≠ reject
  accept_halts : ∀ a : Γ, machine accept a = none
  reject_halts : ∀ a : Γ, machine reject a = none

attribute [instance]
  DTM0.gammaInhabited DTM0.gammaFintype DTM0.gammaDecEq
  DTM0.stateInhabited DTM0.stateFintype DTM0.stateDecEq

namespace DTM0

variable {α : Type u}


def initialLocated (M : DTM0 α) (w : List α) :
    LocatedCfg M.Γ M.State :=
  { cfg := TM0.init (Γ := M.Γ) (Λ := M.State) (encodeInput M.encodeSym w)
    pos := 0 }


def nextLocated (M : DTM0 α)
    (c : LocatedCfg M.Γ M.State) :
    LocatedCfg M.Γ M.State :=
  match M.machine c.cfg.q c.cfg.Tape.head with
  | none => c
  | some (q', stmt) => LocatedCfg.nextOfStmt q' stmt c


def run (M : DTM0 α) (w : List α) :
    ℕ → LocatedCfg M.Γ M.State
  | 0 => M.initialLocated w
  | k + 1 => M.nextLocated (M.run w k)


def Halted (M : DTM0 α) (c : LocatedCfg M.Γ M.State) : Prop :=
  c.cfg.q = M.accept ∨ c.cfg.q = M.reject


def Accepts (M : DTM0 α) (w : List α) : Prop :=
  ∃ k : ℕ, (M.run w k).cfg.q = M.accept


def HaltsOn (M : DTM0 α) (w : List α) : Prop :=
  ∃ k : ℕ, M.Halted (M.run w k)




def Decides (M : DTM0 α) (L : Language α) : Prop :=
  (∀ w : List α, M.HaltsOn w) ∧
    ∀ w : List α, w ∈ L ↔ M.Accepts w




def RunsInTimeBound (M : DTM0 α) (b : ℕ → ℕ) : Prop :=
  ∀ w : List α, ∃ k : ℕ,
    k ≤ b w.length ∧ M.Halted (M.run w k)







def UsesSpaceBoundOn (M : DTM0 α) (w : List α) (s : ℕ) : Prop :=
  w.length ≤ s ∧
    ∀ k : ℕ, HeadWithinSpaceWindow (M.run w k).pos s




def RunsInSpaceBound (M : DTM0 α) (b : ℕ → ℕ) : Prop :=
  ∀ w : List α,
    M.HaltsOn w ∧ M.UsesSpaceBoundOn w (b w.length)

end DTM0





def NatBigO (f g : ℕ → ℕ) : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ => (f n : ℝ))
    (fun n : ℕ => (g n : ℝ))

namespace DTM0

variable {α : Type u}




def RunsInTimeO (M : DTM0 α) (t : ℕ → ℕ) : Prop :=
  ∃ b : ℕ → ℕ, NatBigO b t ∧ M.RunsInTimeBound b




def RunsInSpaceO (M : DTM0 α) (t : ℕ → ℕ) : Prop :=
  ∃ b : ℕ → ℕ, NatBigO b t ∧ M.RunsInSpaceBound b

end DTM0




def TIME (α : Type u) [Fintype α] [DecidableEq α]
    (t : ℕ → ℕ) : Set (Language α) :=
  { L | ∃ M : DTM0 α, M.Decides L ∧ M.RunsInTimeO t }




def SPACE (α : Type u) [Fintype α] [DecidableEq α]
    (t : ℕ → ℕ) : Set (Language α) :=
  { L | ∃ M : DTM0 α, M.Decides L ∧ M.RunsInSpaceO t }






inductive ReachesIn {β : Type u} (R : β → β → Prop) :
    ℕ → β → β → Prop where
  | zero (x : β) : ReachesIn R 0 x x
  | succ {n : ℕ} {x y z : β} :
      R x y → ReachesIn R n y z → ReachesIn R (n + 1) x z















structure NTM0 (α : Type u) where
  Γ : Type u
  [gammaInhabited : Inhabited Γ]
  [gammaFintype : Fintype Γ]
  [gammaDecEq : DecidableEq Γ]
  encodeSym : α → Γ
  encodeSym_injective : Function.Injective encodeSym
  encodeSym_ne_blank : ∀ a : α, encodeSym a ≠ default
  State : Type u
  [stateInhabited : Inhabited State]
  [stateFintype : Fintype State]
  [stateDecEq : DecidableEq State]
  step : State → Γ → Finset (State × TM0.Stmt Γ)
  accept : State
  reject : State
  accept_ne_reject : accept ≠ reject
  accept_halts : ∀ a : Γ, step accept a = ∅
  reject_halts : ∀ a : Γ, step reject a = ∅
  step_total :
    ∀ q a, q ≠ accept → q ≠ reject → (step q a).Nonempty

attribute [instance]
  NTM0.gammaInhabited NTM0.gammaFintype NTM0.gammaDecEq
  NTM0.stateInhabited NTM0.stateFintype NTM0.stateDecEq

namespace NTM0

variable {α : Type u}


def initialLocated (M : NTM0 α) (w : List α) :
    LocatedCfg M.Γ M.State :=
  { cfg := TM0.init (Γ := M.Γ) (Λ := M.State) (encodeInput M.encodeSym w)
    pos := 0 }


def StepRel (M : NTM0 α)
    (c c' : LocatedCfg M.Γ M.State) : Prop :=
  (M.step c.cfg.q c.cfg.Tape.head = ∅ ∧ c' = c) ∨
    ∃ q' stmt,
      (q', stmt) ∈ M.step c.cfg.q c.cfg.Tape.head ∧
        c' = LocatedCfg.nextOfStmt q' stmt c


def Accepts (M : NTM0 α) (w : List α) : Prop :=
  ∃ k : ℕ, ∃ c : LocatedCfg M.Γ M.State,
    ReachesIn M.StepRel k (M.initialLocated w) c ∧
      c.cfg.q = M.accept







def AllBranchesHaltWithin (M : NTM0 α) (w : List α) (k : ℕ) : Prop :=
  ∀ c : LocatedCfg M.Γ M.State,
    ReachesIn M.StepRel k (M.initialLocated w) c →
      c.cfg.q = M.accept ∨ c.cfg.q = M.reject




def Decides (M : NTM0 α) (L : Language α) : Prop :=
  (∀ w : List α, ∃ k : ℕ, M.AllBranchesHaltWithin w k) ∧
    ∀ w : List α, w ∈ L ↔ M.Accepts w




def RunsInTimeBound (M : NTM0 α) (b : ℕ → ℕ) : Prop :=
  ∀ w : List α, M.AllBranchesHaltWithin w (b w.length)




def RunsInTimeO (M : NTM0 α) (t : ℕ → ℕ) : Prop :=
  ∃ b : ℕ → ℕ, NatBigO b t ∧ M.RunsInTimeBound b

end NTM0




def NTIME (α : Type u) [Fintype α] [DecidableEq α]
    (t : ℕ → ℕ) : Set (Language α) :=
  { L | ∃ M : NTM0 α, M.Decides L ∧ M.RunsInTimeO t }





def TIME_twoPowO (α : Type u) [Fintype α] [DecidableEq α]
    (t : ℕ → ℕ) : Set (Language α) :=
  { L | ∃ e : ℕ → ℕ,
      NatBigO e t ∧
        L ∈ TIME α (fun n : ℕ => (2 : ℕ) ^ e n) }




def TIME_expUnion (α : Type u) [Fintype α] [DecidableEq α]
    (t : ℕ → ℕ) : Set (Language α) :=
  { L | ∃ k : ℕ,
      2 ≤ k ∧
        L ∈ TIME α (fun n : ℕ => k ^ t n) }




def P (α : Type u) [Fintype α] [DecidableEq α] :
    Set (Language α) :=
  { L | ∃ k : ℕ, L ∈ TIME α (fun n : ℕ => n ^ k) }




def NP (α : Type u) [Fintype α] [DecidableEq α] :
    Set (Language α) :=
  { L | ∃ k : ℕ, L ∈ NTIME α (fun n : ℕ => n ^ k) }




def PSPACE (α : Type u) [Fintype α] [DecidableEq α] :
    Set (Language α) :=
  { L | ∃ k : ℕ, L ∈ SPACE α (fun n : ℕ => n ^ k) }

section Slide194Statements

variable {α : Type u} [Fintype α] [DecidableEq α]







end Slide194Statements

end Autoform_Introduction_to_the_Theory_of_Computation_computation_slide194_NP_subset_PSPACE
