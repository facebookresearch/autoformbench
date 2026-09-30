import Mathlib

noncomputable section

namespace Autoform_Introduction_to_PDEs_pde_classMeeting4_corollary_1_0_1



def spacetimeCylinder (T : ℝ) (Ω : Set ℝ) : Set (ℝ × ℝ) :=
  Set.prod (Set.Ioo 0 T) Ω



def parabolicBoundary (T : ℝ) (Ω : Set ℝ) : Set (ℝ × ℝ) :=
  Set.prod ({0} : Set ℝ) (closure Ω) ∪
    Set.prod (Set.Ioc 0 T) (frontier Ω)












def IsHeatSolutionOn
    (T D : ℝ) (Ω : Set ℝ)
    (u source : ℝ × ℝ → ℝ) : Prop :=
  let Q := spacetimeCylinder T Ω
  ∃ ut ux uxx : ℝ × ℝ → ℝ,
    ContinuousOn u (closure Q) ∧
    ContinuousOn ut Q ∧
    ContinuousOn ux Q ∧
    ContinuousOn uxx Q ∧
    ∀ p ∈ Q,
      HasDerivAt (fun t : ℝ => u (t, p.2)) (ut p) p.1 ∧
      HasDerivAt (fun x : ℝ => u (p.1, x)) (ux p) p.2 ∧
      HasDerivAt (fun x : ℝ => ux (p.1, x)) (uxx p) p.2 ∧
      ut p - D * uxx p = source p



end Autoform_Introduction_to_PDEs_pde_classMeeting4_corollary_1_0_1
