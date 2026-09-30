import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UnitInterval
import ChallengeDeps

open Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_4_2_7_compactness_of_graphon_space












noncomputable section

open MeasureTheory
open unitInterval

namespace Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_4_2_7_compactness_of_graphon_space























theorem cutDistance_self : ∀ U : Graphon, δ□ U U = 0 := by
  sorry



theorem cutDistance_comm : ∀ U W : Graphon, δ□ U W = δ□ W U := by
  sorry



theorem cutDistance_triangle : ∀ U V W : Graphon, δ□ U W ≤ δ□ U V + δ□ V W := by
  sorry



instance instPseudoMetricSpaceGraphon : PseudoMetricSpace Graphon where
  dist := δ□
  dist_self := cutDistance_self
  dist_comm := cutDistance_comm
  dist_triangle := cutDistance_triangle






abbrev GraphonSpace := SeparationQuotient Graphon

scoped notation "W̃₀" => GraphonSpace






theorem theorem_4_2_7_compactness_of_graphon_space : CompactSpace W̃₀ := by
  sorry

end Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_4_2_7_compactness_of_graphon_space

end