import Mathlib

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace Autoform_Algebraic_Topology_I_alg_top_theorem72

abbrev ZModCat := ModuleCat ℤ

abbrev HObj (n : ℕ) (X : TopCat) : ZModCat :=
  (((singularHomologyFunctor ZModCat n).obj (ModuleCat.of ℤ ℤ)).obj X)

abbrev HMap {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    HObj n X ⟶ HObj n Y :=
  (((singularHomologyFunctor ZModCat n).obj (ModuleCat.of ℤ ℤ)).map f)

def castHomology {X : TopCat} {m n : ℕ} (h : m = n) :
    HObj m X → HObj n X := by
  intro a
  cases h
  exact a

abbrev prodSpace (X Y : TopCat) : TopCat :=
  TopCat.of (↑X × ↑Y)

abbrev prodMap {X X' Y Y' : TopCat} (f : X ⟶ X') (g : Y ⟶ Y') :
    prodSpace X Y ⟶ prodSpace X' Y' :=
  TopCat.ofHom (f.hom.prodMap g.hom)

abbrev leftIncl {X Y : TopCat} (x : ↑X) :
    Y ⟶ prodSpace X Y :=
  TopCat.ofHom ((ContinuousMap.const (↑Y) x).prodMk (ContinuousMap.id (↑Y)))

abbrev rightIncl {X Y : TopCat} (y : ↑Y) :
    X ⟶ prodSpace X Y :=
  TopCat.ofHom ((ContinuousMap.id (↑X)).prodMk (ContinuousMap.const (↑X) y))

abbrev pointSpace : TopCat :=
  TopCat.of PUnit


noncomputable def pointClass : HObj 0 pointSpace :=
  (singularHomologyFunctorZeroOfTotallyDisconnectedSpace
      ZModCat (ModuleCat.of ℤ ℤ) pointSpace).inv
    ((Sigma.ι
        (fun _ : ↑pointSpace => ModuleCat.of ℤ ℤ)
        PUnit.unit)
      (1 : ℤ))


noncomputable def constZeroClass {X : TopCat} (x : ↑X) : HObj 0 X :=
  HMap (TopCat.ofHom (ContinuousMap.const PUnit x)) 0 pointClass



abbrev HomologyCrossFamilyPQ (p q : ℕ) : Type _ :=
  ∀ {X Y : TopCat}, HObj p X →+ HObj q Y →+ HObj (p + q) (prodSpace X Y)

def HomologyCrossNaturalPQ (p q : ℕ) (cross : HomologyCrossFamilyPQ p q) : Prop :=
  ∀ {X X' Y Y' : TopCat}
    (f : X ⟶ X') (g : Y ⟶ Y')
    (a : HObj p X) (b : HObj q Y),
    HMap (prodMap f g) (p + q) (cross a b) =
      cross (HMap f p a) (HMap g q b)

def HomologyCrossAddLeftPQ (p q : ℕ) (cross : HomologyCrossFamilyPQ p q) : Prop :=
  ∀ {X Y : TopCat}
    (a a' : HObj p X) (b : HObj q Y),
    cross (a + a') b = cross a b + cross a' b

def HomologyCrossAddRightPQ (p q : ℕ) (cross : HomologyCrossFamilyPQ p q) : Prop :=
  ∀ {X Y : TopCat}
    (a : HObj p X) (b b' : HObj q Y),
    cross a (b + b') = cross a b + cross a b'

def HomologyCrossNormalizedLeftPQ (p q : ℕ) (cross : HomologyCrossFamilyPQ p q) : Prop :=
  ∀ (hp : p = 0) {X Y : TopCat} (x : ↑X) (b : HObj q Y),
    castHomology (X := prodSpace X Y) (by linarith)
      (cross (castHomology (X := X) hp.symm (constZeroClass x)) b) =
        HMap (leftIncl x) q b

def HomologyCrossNormalizedRightPQ (p q : ℕ) (cross : HomologyCrossFamilyPQ p q) : Prop :=
  ∀ (hq : q = 0) {X Y : TopCat} (a : HObj p X) (y : ↑Y),
    castHomology (X := prodSpace X Y) (by linarith)
      (cross a (castHomology (X := Y) hq.symm (constZeroClass y))) =
        HMap (rightIncl y) p a




def HomologyCrossNontrivialPQ (p q : ℕ) (cross : HomologyCrossFamilyPQ p q) : Prop :=
  ∃ (X Y : TopCat) (a : HObj p X) (b : HObj q Y), cross a b ≠ 0



end Autoform_Algebraic_Topology_I_alg_top_theorem72
