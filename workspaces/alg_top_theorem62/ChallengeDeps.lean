import Mathlib

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace Autoform_Algebraic_Topology_I_alg_top_theorem62

abbrev integralSingularChainComplex (X : TopCat) : ChainComplex (ModuleCat ℤ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X

abbrev SChain (X : TopCat) (n : ℕ) : ModuleCat ℤ :=
  (integralSingularChainComplex X).X n

abbrev SChainMap {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    SChain X n ⟶ SChain Y n :=
  (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map f).f n

abbrev bdry (X : TopCat) (n : ℕ) :
    SChain X (n + 1) ⟶ SChain X n :=
  (integralSingularChainComplex X).d (n + 1) n

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

def castSChain {X : TopCat} {m n : ℕ} (h : m = n) :
    SChain X m → SChain X n := by
  intro a
  cases h
  exact a


abbrev ZeroSimplex (X : TopCat) : Type _ :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0))


noncomputable def zeroSimplexOfPoint {X : TopCat} (x : ↑X) : ZeroSimplex X :=
  (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 0))).symm
    (ContinuousMap.const (stdSimplex ℝ (Fin 1)) x)


noncomputable def constZeroChain {X : TopCat} (x : ↑X) : SChain X 0 :=
  (Sigma.ι
      (fun _ : ZeroSimplex X => ModuleCat.of ℤ ℤ)
      (zeroSimplexOfPoint x))
    (1 : ℤ)

abbrev CrossFamily : Type _ :=
  ∀ {X Y : TopCat}, (p q : ℕ) →
    SChain X p → SChain Y q → SChain (prodSpace X Y) (p + q)

def CrossNatural (cross : CrossFamily) : Prop :=
  ∀ {X X' Y Y' : TopCat}
    (f : X ⟶ X') (g : Y ⟶ Y')
    (p q : ℕ)
    (a : SChain X p) (b : SChain Y q),
    SChainMap (prodMap f g) (p + q) (cross p q a b) =
      cross p q (SChainMap f p a) (SChainMap g q b)

def CrossAddLeft (cross : CrossFamily) : Prop :=
  ∀ {X Y : TopCat} (p q : ℕ)
    (a a' : SChain X p) (b : SChain Y q),
    cross p q (a + a') b = cross p q a b + cross p q a' b

def CrossAddRight (cross : CrossFamily) : Prop :=
  ∀ {X Y : TopCat} (p q : ℕ)
    (a : SChain X p) (b b' : SChain Y q),
    cross p q a (b + b') = cross p q a b + cross p q a b'

def CrossLeibniz (cross : CrossFamily) : Prop :=
  ∀ {X Y : TopCat} (p q : ℕ)
    (a : SChain X (p + 1)) (b : SChain Y (q + 1)),
    bdry (prodSpace X Y) (p + q + 1) (castSChain (by linarith) (cross (p + 1) (q + 1) a b)) =
      castSChain (by linarith) (cross p (q + 1) (bdry X p a) b) +
        ((-1 : ℤ) ^ (p + 1)) • castSChain (by linarith) (cross (p + 1) q a (bdry Y q b))

def CrossNormalizedLeft (cross : CrossFamily) : Prop :=
  ∀ {X Y : TopCat} (x : ↑X) (q : ℕ) (b : SChain Y q),
    castSChain (by simp) (cross 0 q (constZeroChain x) b) =
      SChainMap (leftIncl x) q b

def CrossNormalizedRight (cross : CrossFamily) : Prop :=
  ∀ {X Y : TopCat} (y : ↑Y) (p : ℕ) (a : SChain X p),
    castSChain (by simp) (cross p 0 a (constZeroChain y)) =
      SChainMap (rightIncl y) p a



end Autoform_Algebraic_Topology_I_alg_top_theorem62
