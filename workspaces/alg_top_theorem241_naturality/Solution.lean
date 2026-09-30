


import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Module.PUnit
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Submission
import ChallengeDeps














noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace Autoform_Algebraic_Topology_I_alg_top_theorem241_naturality

















































noncomputable instance pid_moduleCat_hasProjectiveResolutions
    (R : Type) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] :
    HasProjectiveResolutions (RModCat R) := Submission.Autoform_Algebraic_Topology_I_alg_top_theorem241_naturality.pid_moduleCat_hasProjectiveResolutions R

































theorem theorem241
    (R : Type) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] :
    Nonempty (UniversalCoefficientTheoremPackage R) := Submission.Autoform_Algebraic_Topology_I_alg_top_theorem241_naturality.theorem241 R










theorem theorem241_component
    {R : Type} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (C : RChainComplex R) (hC : DegreewiseFree C)
    (M : RModCat R) (n : ℕ) :
    ∃ S : UniversalCoefficientShortExact C M n, True := by
  rcases theorem241 R with ⟨UCT⟩
  exact ⟨UCT.sequence C hC M n, trivial⟩








theorem theorem241_alpha_formula
    {R : Type} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (C : RChainComplex R) (hC : DegreewiseFree C)
    (M : RModCat R) (n : ℕ) :
    ∃ S : UniversalCoefficientShortExact C M n,
      IsUCTComparisonMap C M n S.alpha := by
  rcases theorem241_component C hC M n with ⟨S, _⟩
  exact ⟨S, S.alpha_spec⟩







theorem theorem241_shortExact
    {R : Type} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (C : RChainComplex R) (hC : DegreewiseFree C)
    (M : RModCat R) (n : ℕ) :
    ∃ alpha :
      TensorObj (ChainHomology C n) M ⟶
        TensorComplexHomology C M n,
    ∃ boundary :
      TensorComplexHomology C M n ⟶
        TorOne (PreviousHomology C n) M,
      IsUCTComparisonMap C M n alpha ∧
      ShortExactModuleSequence alpha boundary := by
  rcases theorem241_component C hC M n with ⟨S, _⟩
  exact ⟨S.alpha, S.boundary, S.alpha_spec, S.shortExact⟩










theorem theorem241_splits
    {R : Type} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (C : RChainComplex R) (hC : DegreewiseFree C)
    (M : RModCat R) (n : ℕ) :
    ∃ S : UniversalCoefficientShortExact C M n,
      ShortExactSequenceSplits S.alpha S.boundary := by
  rcases theorem241_component C hC M n with ⟨S, _⟩
  exact ⟨S, S.split⟩







theorem theorem241_naturality
    {R : Type} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    {C D : RChainComplex R}
    (hC : DegreewiseFree C) (hD : DegreewiseFree D)
    {M N : RModCat R}
    (n : ℕ) (fC : C ⟶ D) (fM : M ⟶ N) :
    ∃ SC : UniversalCoefficientShortExact C M n,
    ∃ SD : UniversalCoefficientShortExact D N n,
      UCTNaturality SC SD fC fM := by
  rcases theorem241 R with ⟨UCT⟩
  refine ⟨UCT.sequence C hC M n,
    UCT.sequence D hD N n, ?_⟩
  exact UCT.naturality hC hD n fC fM

end Autoform_Algebraic_Topology_I_alg_top_theorem241_naturality

end
