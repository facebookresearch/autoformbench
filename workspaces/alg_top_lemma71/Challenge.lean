import ChallengeDeps

open Autoform_Algebraic_Topology_I_alg_top_lemma71

theorem lemma71 {A B C : ZChainComplex}
    (cp : ChainCrossData A B C)
    (p q : ℕ) :
    ∃! φ : A.homology p →+ B.homology q →+ C.homology (p + q),
      IsInducedByChainCross cp p q φ := by
  sorry
