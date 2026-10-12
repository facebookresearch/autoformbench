/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace Autoform_Algebraic_Topology_I_alg_top_lemma71


abbrev ZChainComplex := ChainComplex (ModuleCat ℤ) ℤ


def castChain {A : ZChainComplex} {m n : ℤ} (h : m = n) :
    A.X m → A.X n := by
  intro a
  cases h
  exact a








abbrev ChainCrossFamily (A B C : ZChainComplex) : Type _ :=
  ∀ p q : ℤ, A.X p → B.X q → C.X (p + q)

def ChainCrossAddLeft {A B C : ZChainComplex} (cross : ChainCrossFamily A B C) : Prop :=
  ∀ (p q : ℤ) (a a' : A.X p) (b : B.X q),
    cross p q (a + a') b = cross p q a b + cross p q a' b

def ChainCrossAddRight {A B C : ZChainComplex} (cross : ChainCrossFamily A B C) : Prop :=
  ∀ (p q : ℤ) (a : A.X p) (b b' : B.X q),
    cross p q a (b + b') = cross p q a b + cross p q a b'







def ChainCrossLeibniz {A B C : ZChainComplex} (cross : ChainCrossFamily A B C) : Prop :=
  ∀ (p q : ℕ) (a : A.X (p : ℤ)) (b : B.X (q : ℤ)),
    C.d ((p : ℤ) + (q : ℤ)) (((p : ℤ) + (q : ℤ)) - 1)
        (cross (p : ℤ) (q : ℤ) a b) =
      castChain (A := C) (by ring)
        (cross ((p : ℤ) - 1) (q : ℤ)
          (A.d (p : ℤ) ((p : ℤ) - 1) a) b) +
        ((-1 : ℤ) ^ p) •
          castChain (A := C) (by ring)
            (cross (p : ℤ) ((q : ℤ) - 1)
              a (B.d (q : ℤ) ((q : ℤ) - 1) b))

structure ChainCrossData (A B C : ZChainComplex) where
  cross : ChainCrossFamily A B C
  add_left : ChainCrossAddLeft cross
  add_right : ChainCrossAddRight cross
  leibniz : ChainCrossLeibniz cross

def IsInducedByChainCross
    {A B C : ZChainComplex}
    (cp : ChainCrossData A B C)
    (p q : ℕ)
    (φ : A.homology p →+ B.homology q →+ C.homology (p + q)) : Prop :=
  ∀ (za : A.cycles p) (zb : B.cycles q),
    ∃ zc : C.cycles (p + q),
      C.iCycles (p + q) zc =
        castChain (A := C) (by rfl)
          (cp.cross (p : ℤ) (q : ℤ) (A.iCycles p za) (B.iCycles q zb))
      ∧
      φ (A.homologyπ p za) (B.homologyπ q zb) =
        C.homologyπ (p + q) zc



end Autoform_Algebraic_Topology_I_alg_top_lemma71
