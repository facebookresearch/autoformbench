import Mathlib

































universe u v w
namespace Autoform_Introduction_to_the_Theory_of_Computation_computation_isPushdown














structure PDA (α : Type u) (Γ : Type v) (σ : Type w) where
  

  step : σ → Option α → Option Γ → Set (σ × List Γ)
  
  start : σ
  
  startStack : List Γ
  
  accept : Set σ

namespace PDA

variable {α : Type u} {Γ : Type v} {σ : Type w}






structure Config (α : Type u) (Γ : Type v) (σ : Type w) where
  
  state : σ
  
  input : List α
  
  stack : List Γ

variable (M : PDA α Γ σ)









inductive Step : Config α Γ σ → Config α Γ σ → Prop
  
  | eps_empty {q q' : σ} {input : List α} {push : List Γ}
      (h : (q', push) ∈ M.step q none none) :
      Step { state := q, input := input, stack := [] }
           { state := q', input := input, stack := push }
  
  | eps_pop {q q' : σ} {input : List α} {γ : Γ} {stack push : List Γ}
      (h : (q', push) ∈ M.step q none (some γ)) :
      Step { state := q, input := input, stack := γ :: stack }
           { state := q', input := input, stack := push ++ stack }
  
  | read_empty {q q' : σ} {a : α} {input : List α} {push : List Γ}
      (h : (q', push) ∈ M.step q (some a) none) :
      Step { state := q, input := a :: input, stack := [] }
           { state := q', input := input, stack := push }
  
  | read_pop {q q' : σ} {a : α} {input : List α} {γ : Γ} {stack push : List Γ}
      (h : (q', push) ∈ M.step q (some a) (some γ)) :
      Step { state := q, input := a :: input, stack := γ :: stack }
           { state := q', input := input, stack := push ++ stack }






abbrev Reaches : Config α Γ σ → Config α Γ σ → Prop :=
  Relation.ReflTransGen M.Step








def AcceptsConfig (c : Config α Γ σ) : Prop :=
  c.input = [] ∧ c.state ∈ M.accept





def acceptsFrom (s : σ) (stack : List Γ) : Language α :=
  { x | ∃ c, M.Reaches { state := s, input := x, stack := stack } c ∧ M.AcceptsConfig c }





def accepts : Language α :=
  M.acceptsFrom M.start M.startStack








def Finitary : Prop :=
  ∀ q i top, (M.step q i top).Finite

end PDA

namespace Language










def IsPushdown {α : Type u} (L : Language α) : Prop :=
  ∃ (Γ : Type) (_ : Fintype Γ) (σ : Type) (_ : Fintype σ),
    ∃ M : PDA α Γ σ, M.Finitary ∧ M.accepts = L



end Language

end Autoform_Introduction_to_the_Theory_of_Computation_computation_isPushdown
