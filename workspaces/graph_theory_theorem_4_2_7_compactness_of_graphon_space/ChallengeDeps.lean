import Mathlib













noncomputable section

open MeasureTheory
open unitInterval

namespace Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_4_2_7_compactness_of_graphon_space


structure Graphon where
  toFun : I × I → I
  measurable_toFun : Measurable toFun
  symm : ∀ x y : I, toFun (x, y) = toFun (y, x)

instance instCoeFunGraphon : CoeFun Graphon (fun _ => I × I → I) := ⟨Graphon.toFun⟩


def cutNorm (W : I × I → ℝ) : ℝ :=
  sSup
    {r : ℝ |
      ∃ S T : Set I,
        MeasurableSet S ∧
        MeasurableSet T ∧
        r = |∫ z in S ×ˢ T, W z ∂(volume : Measure (I × I))|}


abbrev IsMeasurePreserving (φ : I → I) : Prop :=
  MeasurePreserving φ volume volume


def IsInvertibleMeasurePreserving (φ : I → I) : Prop :=
  IsMeasurePreserving φ ∧
    ∃ ψ : I → I,
      IsMeasurePreserving ψ ∧
        (φ ∘ ψ) =ᵐ[volume] id ∧
        (ψ ∘ φ) =ᵐ[volume] id


def relabel (W : I × I → ℝ) (φ : I → I) : I × I → ℝ :=
  fun p => W (φ p.1, φ p.2)


def cutDistance (U W : Graphon) : ℝ :=
  sInf
    {r : ℝ |
      ∃ φ : I → I,
        IsInvertibleMeasurePreserving φ ∧
          r = cutNorm (fun p => (U p : ℝ) - relabel (fun q => (W q : ℝ)) φ p)}

scoped notation "δ□" => cutDistance



















end Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_4_2_7_compactness_of_graphon_space

end