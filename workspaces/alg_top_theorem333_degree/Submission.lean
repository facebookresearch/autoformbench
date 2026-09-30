


import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic
import Submission.Helpers
import ChallengeDeps





















namespace Submission

open _root_.Autoform_Algebraic_Topology_I_alg_top_theorem333_degree
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open scoped BigOperators

namespace Autoform_Algebraic_Topology_I_alg_top_theorem333_degree













abbrev SingCCMap
    (R : Type) [CommRing R] {X Y : TopCat} (f : X ⟶ Y) :
    SingCC R X ⟶ SingCC R Y :=
  ((singularChainComplexFunctor (RModCat R)).obj
      (CoeffModule R)).map f





































theorem frontFaceMap_existsUnique (p q : ℕ) :
    ∃! f : StdSimplexTop p ⟶ StdSimplexTop (p + q),
      IsFrontFaceMap p q f := by
  sorry










noncomputable def frontFaceMap (p q : ℕ) :
    StdSimplexTop p ⟶ StdSimplexTop (p + q) :=
  Classical.choose (frontFaceMap_existsUnique p q)






theorem frontFaceMap_spec (p q : ℕ) :
    IsFrontFaceMap p q (frontFaceMap p q) :=
  (Classical.choose_spec (frontFaceMap_existsUnique p q)).1









theorem backFaceMap_existsUnique (p q : ℕ) :
    ∃! f : StdSimplexTop q ⟶ StdSimplexTop (p + q),
      IsBackFaceMap p q f := by
  sorry










noncomputable def backFaceMap (p q : ℕ) :
    StdSimplexTop q ⟶ StdSimplexTop (p + q) :=
  Classical.choose (backFaceMap_existsUnique p q)






theorem backFaceMap_spec (p q : ℕ) :
    IsBackFaceMap p q (backFaceMap p q) :=
  (Classical.choose_spec (backFaceMap_existsUnique p q)).1
















noncomputable def frontFaceSimplex
    {X Y : TopCat} (p q : ℕ)
    (σ : SingularSimplex (ProductSpace X Y) (p + q)) :
    SingularSimplex X p :=
  singularSimplexOfMap
    (frontFaceMap p q ≫ simplexMapOf σ ≫ productFst X Y)







noncomputable def backFaceSimplex
    {X Y : TopCat} (p q : ℕ)
    (σ : SingularSimplex (ProductSpace X Y) (p + q)) :
    SingularSimplex Y q :=
  singularSimplexOfMap
    (backFaceMap p q ≫ simplexMapOf σ ≫ productSnd X Y)








theorem cochainDifferential_map_add
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ)
    (φ ψ : SingChain R X n ⟶ CoeffModule R) :
    ((-1 : R) ^ (n + 1)) • ((SingCC R X).d (n + 1) n ≫ (φ + ψ)) =
      ((-1 : R) ^ (n + 1)) • ((SingCC R X).d (n + 1) n ≫ φ) +
        ((-1 : R) ^ (n + 1)) • ((SingCC R X).d (n + 1) n ≫ ψ) := by
  sorry









theorem cochainDifferential_map_smul
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ) (r : R)
    (φ : SingChain R X n ⟶ CoeffModule R) :
    ((-1 : R) ^ (n + 1)) • ((SingCC R X).d (n + 1) n ≫ (r • φ)) =
      (RingHom.id R) r • (((-1 : R) ^ (n + 1)) • ((SingCC R X).d (n + 1) n ≫ φ)) := by
  sorry














noncomputable def cochainDifferential
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ) :
    CochainGroup R X n ⟶ CochainGroup R X (n + 1) :=
  ModuleCat.ofHom
    { toFun := fun φ =>
        ((-1 : R) ^ (n + 1)) •
          ((SingCC R X).d (n + 1) n ≫ φ)
      map_add' := fun φ ψ => cochainDifferential_map_add R X n φ ψ
      map_smul' := fun r φ => cochainDifferential_map_smul R X n r φ }






theorem SingularCochainComplex_shape
    (R : Type) [CommRing R] (X : TopCat) (i j : ℕ)
    (hij : ¬ (ComplexShape.up ℕ).Rel i j) :
    (if h : j = i + 1 then
        cochainDifferential R X i ≫
          eqToHom (by
            cases h
            rfl)
      else 0) = (0 : CochainGroup R X i ⟶ CochainGroup R X j) := by
  sorry








theorem SingularCochainComplex_d_comp_d
    (R : Type) [CommRing R] (X : TopCat) (i j k : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j)
    (hjk : (ComplexShape.up ℕ).Rel j k) :
    ((if h : j = i + 1 then
        cochainDifferential R X i ≫
          eqToHom (by
            cases h
            rfl)
      else 0) ≫
      (if h : k = j + 1 then
        cochainDifferential R X j ≫
          eqToHom (by
            cases h
            rfl)
      else 0)) = (0 : CochainGroup R X i ⟶ CochainGroup R X k) := by
  sorry





















noncomputable def SingularCochainComplex
    (R : Type) [CommRing R] (X : TopCat) :
    CochainComplex (RModCat R) ℕ where
  X n := CochainGroup R X n
  d i j :=
    if h : j = i + 1 then
      cochainDifferential R X i ≫
        eqToHom (by
          cases h
          rfl)
    else
      0
  shape := fun i j hij => SingularCochainComplex_shape R X i j hij
  d_comp_d' := fun i j k hij hjk =>
    SingularCochainComplex_d_comp_d R X i j k hij hjk








abbrev SingularCohomology
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ) :
    RModCat R :=
  (SingularCochainComplex R X).homology n













def IsCochainCrossProduct
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ)
    (cross :
      TensorObj (CochainGroup R X p) (CochainGroup R Y q) ⟶
        CochainGroup R (ProductSpace X Y) (p + q)) : Prop :=
  ∀ (f : ↑(CochainGroup R X p))
    (g : ↑(CochainGroup R Y q))
    (σ : SingularSimplex (ProductSpace X Y) (p + q)),
    evalCochain (R := R)
        (cross (pureTensor (R := R) f g)) σ =
      koszulSign R (p * q) *
        evalCochain (R := R) f (frontFaceSimplex p q σ) *
          evalCochain (R := R) g (backFaceSimplex p q σ)






theorem cochainCrossProduct_existsUnique
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ) :
    ∃! cross :
      TensorObj (CochainGroup R X p) (CochainGroup R Y q) ⟶
        CochainGroup R (ProductSpace X Y) (p + q),
      IsCochainCrossProduct R X Y p q cross := by
  sorry










noncomputable def cochainCrossProduct
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ) :
    TensorObj (CochainGroup R X p) (CochainGroup R Y q) ⟶
      CochainGroup R (ProductSpace X Y) (p + q) :=
  Classical.choose
    (cochainCrossProduct_existsUnique R X Y p q)






theorem cochainCrossProduct_spec
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ) :
    IsCochainCrossProduct R X Y p q
      (cochainCrossProduct R X Y p q) :=
  (Classical.choose_spec
    (cochainCrossProduct_existsUnique R X Y p q)).1












def IsCohomologyCrossProduct
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ)
    (cross :
      TensorObj (SingularCohomology R X p)
        (SingularCohomology R Y q) ⟶
          SingularCohomology R (ProductSpace X Y) (p + q)) : Prop :=
  ∀ (fx : ↑((SingularCochainComplex R X).cycles p))
    (gy : ↑((SingularCochainComplex R Y).cycles q)),
    ∃ hxy :
      ↑((SingularCochainComplex R (ProductSpace X Y)).cycles (p + q)),
      ((SingularCochainComplex R (ProductSpace X Y)).iCycles
          (p + q)) hxy =
        cochainCrossProduct R X Y p q
          (pureTensor (R := R)
            (((SingularCochainComplex R X).iCycles p) fx)
            (((SingularCochainComplex R Y).iCycles q) gy))
      ∧
      cross
          (pureTensor (R := R)
            ((SingularCochainComplex R X).homologyπ p fx)
            ((SingularCochainComplex R Y).homologyπ q gy)) =
        (SingularCochainComplex R (ProductSpace X Y)).homologyπ
          (p + q) hxy








theorem cohomologyCrossProduct_existsUnique
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ) :
    ∃! cross :
      TensorObj (SingularCohomology R X p)
        (SingularCohomology R Y q) ⟶
          SingularCohomology R (ProductSpace X Y) (p + q),
      IsCohomologyCrossProduct R X Y p q cross := by
  sorry













noncomputable def cohomologyCrossProduct
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ) :
    TensorObj (SingularCohomology R X p)
      (SingularCohomology R Y q) ⟶
        SingularCohomology R (ProductSpace X Y) (p + q) :=
  Classical.choose
    (cohomologyCrossProduct_existsUnique R X Y p q)






theorem cohomologyCrossProduct_spec
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ) :
    IsCohomologyCrossProduct R X Y p q
      (cohomologyCrossProduct R X Y p q) :=
  (Classical.choose_spec
    (cohomologyCrossProduct_existsUnique R X Y p q)).1








def degreeCast
    (R : Type) [CommRing R]
    (X : TopCat) {m n : ℕ} (h : m = n)
    (x : ↑(SingularCohomology R X m)) :
    ↑(SingularCohomology R X n) := by
  cases h
  exact x





















abbrev CohomologyKunnethSummand
    (R : Type) [CommRing R] (X Y : TopCat) (n : ℕ)
    (i : Fin (n + 1)) :
    RModCat R :=
  TensorObj
    (SingularCohomology R X i.1)
    (SingularCohomology R Y (n - i.1))













abbrev CohomologyKunnethSource
    (R : Type) [CommRing R] (X Y : TopCat) (n : ℕ) :
    RModCat R :=
  ∐ (fun i : Fin (n + 1) =>
    CohomologyKunnethSummand R X Y n i)











noncomputable def cohomologyCrossProductTotalDegreeComponent
    (R : Type) [CommRing R] (X Y : TopCat) (n : ℕ)
    (i : Fin (n + 1)) :
    CohomologyKunnethSummand R X Y n i ⟶
      SingularCohomology R (ProductSpace X Y) n :=
  cohomologyCrossProduct R X Y i.1 (n - i.1) ≫
    eqToHom (by
      rw [finDegreeSum n i])













noncomputable def cohomologyCrossProductTotalDegree
    (R : Type) [CommRing R] (X Y : TopCat) (n : ℕ) :
    CohomologyKunnethSource R X Y n ⟶
      SingularCohomology R (ProductSpace X Y) n :=
  Sigma.desc
    (fun i : Fin (n + 1) =>
      cohomologyCrossProductTotalDegreeComponent R X Y n i)







theorem cohomologyCrossProductTotalDegree_on_summand
    (R : Type) [CommRing R] (X Y : TopCat) (n : ℕ)
    (i : Fin (n + 1)) :
    Sigma.ι
        (fun j : Fin (n + 1) =>
          CohomologyKunnethSummand R X Y n j) i ≫
      cohomologyCrossProductTotalDegree R X Y n =
    cohomologyCrossProductTotalDegreeComponent R X Y n i := by
  sorry











def CohomologyCrossProductIsomorphism
    (R : Type) [CommRing R] (X Y : TopCat) : Prop :=
  ∀ n : ℕ, IsIso (cohomologyCrossProductTotalDegree R X Y n)



















theorem theorem333
    (R : Type) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (X Y : TopCat)
    (hX : HomologyOfXFiniteFree R X) :
    CohomologyCrossProductIsomorphism R X Y := by
  sorry







theorem theorem333_degree
    (R : Type) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (X Y : TopCat)
    (hX : HomologyOfXFiniteFree R X)
    (n : ℕ) :
    IsIso (cohomologyCrossProductTotalDegree R X Y n) :=
  theorem333 R X Y hX n

end Autoform_Algebraic_Topology_I_alg_top_theorem333_degree


end
end Submission