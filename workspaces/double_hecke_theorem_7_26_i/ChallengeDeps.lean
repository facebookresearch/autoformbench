/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

























noncomputable section

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_7_26_i

open scoped BigOperators

universe u

variable {B : Type u} [Finite B]









abbrev W (M : CoxeterMatrix B) : Type u := M.Group


abbrev CoxeterWord : Type u := List B







def CoxeterWord.eval (M : CoxeterMatrix B) (ω : CoxeterWord (B := B)) : W M :=
  M.toCoxeterSystem.wordProd ω






def IsReducedWord (M : CoxeterMatrix B) (ω : CoxeterWord (B := B)) : Prop :=
  ∀ υ : CoxeterWord,
    CoxeterWord.eval M υ = CoxeterWord.eval M ω → ω.length ≤ υ.length






structure ReducedWordChoice (M : CoxeterMatrix B) where
  word : W M → CoxeterWord
  represents : ∀ x : W M, CoxeterWord.eval M (word x) = x
  reduced : ∀ x : W M, IsReducedWord M (word x)








def negFin {n : ℕ} (hn : n ≠ 0) (k : Fin n) : Fin n :=
  ⟨(n - k.val) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩










structure ParameterIndex (M : CoxeterMatrix B) where
  i : B
  j : B
  off : i ≠ j
  finite : M i j ≠ 0
  k : Fin (M i j)

namespace ParameterIndex

variable {M : CoxeterMatrix B}





def swap (p : ParameterIndex M) : ParameterIndex M :=
  { i := p.j
    j := p.i
    off := p.off.symm
    finite := by
      rw [← M.symmetric p.i p.j]
      exact p.finite
    k := Fin.cast (M.symmetric p.i p.j) p.k }





def negSwap (p : ParameterIndex M) : ParameterIndex M :=
  { i := p.j
    j := p.i
    off := p.off.symm
    finite := by
      rw [← M.symmetric p.i p.j]
      exact p.finite
    k := Fin.cast (M.symmetric p.i p.j) (negFin p.finite p.k) }

end ParameterIndex







inductive ParameterLetter (M : CoxeterMatrix B) where
  | pos : ParameterIndex M → ParameterLetter M
  | inv : ParameterIndex M → ParameterLetter M





inductive HeckeGen (M : CoxeterMatrix B) where
  | s : B → HeckeGen M
  | t : ParameterIndex M → HeckeGen M
  | tinv : ParameterIndex M → HeckeGen M






abbrev FreeHeckeAlgebra (M : CoxeterMatrix B) : Type u :=
  FreeAlgebra ℂ (HeckeGen M)


def freeGen (M : CoxeterMatrix B) (g : HeckeGen M) : FreeHeckeAlgebra M :=
  FreeAlgebra.ι ℂ g


def ParameterLetter.toGen {M : CoxeterMatrix B} :
    ParameterLetter M → HeckeGen M
  | ParameterLetter.pos p => HeckeGen.t p
  | ParameterLetter.inv p => HeckeGen.tinv p


def freeParam (M : CoxeterMatrix B) (a : ParameterLetter M) :
    FreeHeckeAlgebra M :=
  freeGen M a.toGen






def orderedFinProduct {A : Type*} [Monoid A] {n : ℕ}
    (f : Fin n → A) : A :=
  (List.ofFn f).prod





inductive heckeRel (M : CoxeterMatrix B) :
    FreeHeckeAlgebra M → FreeHeckeAlgebra M → Prop
  
  | s_sq (i : B) :
      heckeRel M
        (freeGen M (HeckeGen.s i) * freeGen M (HeckeGen.s i))
        1
  
  | t_left_inv (p : ParameterIndex M) :
      heckeRel M
        (freeGen M (HeckeGen.t p) * freeGen M (HeckeGen.tinv p))
        1
  
  | t_right_inv (p : ParameterIndex M) :
      heckeRel M
        (freeGen M (HeckeGen.tinv p) * freeGen M (HeckeGen.t p))
        1
  
  | t_orientation (p : ParameterIndex M) :
      heckeRel M
        (freeGen M (HeckeGen.t p))
        (freeGen M (HeckeGen.tinv p.negSwap))
  
  | tinv_orientation (p : ParameterIndex M) :
      heckeRel M
        (freeGen M (HeckeGen.tinv p))
        (freeGen M (HeckeGen.t p.negSwap))
  
  | param_comm (a b : ParameterLetter M) :
      heckeRel M
        (freeParam M a * freeParam M b)
        (freeParam M b * freeParam M a)
  
  | s_t_twist (p : B) (q : ParameterIndex M) :
      heckeRel M
        (freeGen M (HeckeGen.s p) * freeGen M (HeckeGen.t q))
        (freeGen M (HeckeGen.t q.swap) * freeGen M (HeckeGen.s p))
  
  | s_tinv_twist (p : B) (q : ParameterIndex M) :
      heckeRel M
        (freeGen M (HeckeGen.s p) * freeGen M (HeckeGen.tinv q))
        (freeGen M (HeckeGen.tinv q.swap) * freeGen M (HeckeGen.s p))
  




  | braid_polynomial (i j : B) (hij : i ≠ j) (hfin : M i j ≠ 0) :
      heckeRel M
        (orderedFinProduct
          (fun k : Fin (M i j) =>
            freeGen M (HeckeGen.s i) * freeGen M (HeckeGen.s j)
              - freeGen M
                  (HeckeGen.t
                    { i := i
                      j := j
                      off := hij
                      finite := hfin
                      k := k })))
        0








abbrev CoxeterHeckeAlgebra (M : CoxeterMatrix B) : Type u :=
  RingQuot (heckeRel M)

namespace CoxeterHeckeAlgebra

variable (M : CoxeterMatrix B)


def mk : FreeHeckeAlgebra M →+* CoxeterHeckeAlgebra M :=
  RingQuot.mkRingHom (heckeRel M)


def Tsimple (i : B) : CoxeterHeckeAlgebra M :=
  mk M (freeGen M (HeckeGen.s i))


def Tparam (p : ParameterIndex M) : CoxeterHeckeAlgebra M :=
  mk M (freeGen M (HeckeGen.t p))


def TparamInv (p : ParameterIndex M) : CoxeterHeckeAlgebra M :=
  mk M (freeGen M (HeckeGen.tinv p))







def Tword (ω : CoxeterWord (B := B)) : CoxeterHeckeAlgebra M :=
  (ω.map (fun i => Tsimple M i)).prod



def parameterSet : Set (CoxeterHeckeAlgebra M) :=
  Set.range (Tparam M) ∪ Set.range (TparamInv M)












def parameterSubring : Subalgebra ℂ (CoxeterHeckeAlgebra M) :=
  Algebra.adjoin ℂ (parameterSet M)





instance parameterSubringModule :
    Module (parameterSubring M) (CoxeterHeckeAlgebra M) where
  smul r a := (r : CoxeterHeckeAlgebra M) * a
  one_smul := by
    intro a
    change (1 : CoxeterHeckeAlgebra M) * a = a
    exact one_mul a
  mul_smul := by
    intro r s a
    change ((r : CoxeterHeckeAlgebra M) * (s : CoxeterHeckeAlgebra M)) * a =
      (r : CoxeterHeckeAlgebra M) * ((s : CoxeterHeckeAlgebra M) * a)
    exact mul_assoc _ _ _
  smul_zero := by
    intro r
    change (r : CoxeterHeckeAlgebra M) * 0 = 0
    exact mul_zero _
  smul_add := by
    intro r a b
    change (r : CoxeterHeckeAlgebra M) * (a + b) =
      (r : CoxeterHeckeAlgebra M) * a + (r : CoxeterHeckeAlgebra M) * b
    exact left_distrib _ _ _
  zero_smul := by
    intro a
    change (0 : CoxeterHeckeAlgebra M) * a = 0
    exact zero_mul _
  add_smul := by
    intro r s a
    change ((r : CoxeterHeckeAlgebra M) + (s : CoxeterHeckeAlgebra M)) * a =
      (r : CoxeterHeckeAlgebra M) * a + (s : CoxeterHeckeAlgebra M) * a
    exact right_distrib _ _ _

end CoxeterHeckeAlgebra

open CoxeterHeckeAlgebra

variable (M : CoxeterMatrix B)



end Autoform_Double_Hecke_Algebras_double_hecke_theorem_7_26_i
