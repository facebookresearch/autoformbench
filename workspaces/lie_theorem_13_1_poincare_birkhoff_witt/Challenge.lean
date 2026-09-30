import ChallengeDeps





import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Data.List.Basic

open Autoform_Lie_groups_lie_algebras_lie_theorem_13_1_poincare_birkhoff_witt
open scoped DirectSum

universe u v

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_13_1_poincare_birkhoff_witt





section AssociatedGraded

variable {k : Type u} {A : Type v}
variable [CommRing k] [Ring A] [Algebra k A]















def ueaWord
    (k : Type u) (L : Type v)
    [CommRing k] [LieRing L] [LieAlgebra k L] :
    List L → UniversalEnvelopingAlgebra k L
  | [] => 1
  | x :: xs => (UniversalEnvelopingAlgebra.ι k x) * ueaWord k L xs







structure AlgebraFiltration
    (k : Type u) (A : Type v)
    [CommRing k] [Ring A] [Algebra k A] where
  F : ℕ → Submodule k A
  mono : ∀ {i j : ℕ}, i ≤ j → F i ≤ F j
  one_mem : (1 : A) ∈ F 0
  union_all : ⋃ n : ℕ, (F n).carrier = ⊤
  mul_mem :
    ∀ {i j : ℕ} {a b : A}, a ∈ F i → b ∈ F j → a * b ∈ F (i + j)
  commutator_mem_lower :
    ∀ {i j : ℕ} {a b : A}, a ∈ F i → b ∈ F j →
      a * b - b * a ∈
        match i + j with
        | 0 => ⊥
        | n + 1 => F n



def lower (F : AlgebraFiltration k A) (n : ℕ) :
    Submodule k (F.F n) :=
  match n with
  | 0 => ⊥
  | m + 1 => (F.F m).comap (Submodule.subtype (F.F (m + 1)))


abbrev piece (F : AlgebraFiltration k A) (n : ℕ) : Type v :=
  F.F n ⧸ lower F n


abbrev associatedGraded (F : AlgebraFiltration k A) : Type v :=
  DirectSum ℕ (piece F)


def mk (F : AlgebraFiltration k A) (n : ℕ) (a : A) (ha : a ∈ F.F n) :
    piece F n :=
  Submodule.Quotient.mk (p := lower F n) ⟨a, ha⟩



theorem pieceMul_wellDefined
    (F : AlgebraFiltration k A) (i j : ℕ)
    (a₁ : F.F i) (b₁ : F.F j) (a₂ : F.F i) (b₂ : F.F j)
    (ha : (lower F i).quotientRel a₁ a₂)
    (hb : (lower F j).quotientRel b₁ b₂) :
    mk F (i + j) (a₁.1 * b₁.1) (F.mul_mem a₁.2 b₁.2)
      = mk F (i + j) (a₂.1 * b₂.1) (F.mul_mem a₂.2 b₂.2) := by
  
  
  
  
  sorry






































noncomputable def pieceMul
    (F : AlgebraFiltration k A) (i j : ℕ) :
    piece F i → piece F j → piece F (i + j) :=
  Quotient.lift₂
    (fun (a : F.F i) (b : F.F j) =>
      mk F (i + j) (a.1 * b.1) (F.mul_mem a.2 b.2))
    (fun a b a' b' ha hb => pieceMul_wellDefined F i j a b a' b' ha hb)







def ofPiece (F : AlgebraFiltration k A) (n : ℕ)
    (x : piece F n) : associatedGraded F :=
  (DFinsupp.single n x : DirectSum ℕ (piece F))


noncomputable def mul (F : AlgebraFiltration k A) :
    associatedGraded F → associatedGraded F → associatedGraded F := by
  classical
  exact fun x y =>
    DFinsupp.sum x fun i xi =>
      DFinsupp.sum y fun j yj =>
        ofPiece F (i + j) (pieceMul F i j xi yj)


def one (F : AlgebraFiltration k A) : associatedGraded F :=
  ofPiece F 0 (mk F 0 (1 : A) F.one_mem)

theorem commSemiring_zero_add (F : AlgebraFiltration k A)
    (a : associatedGraded F) : 0 + a = a := by
  sorry


theorem commSemiring_add_zero (F : AlgebraFiltration k A)
    (a : associatedGraded F) : a + 0 = a := by
  sorry


theorem commSemiring_add_assoc (F : AlgebraFiltration k A)
    (a b c : associatedGraded F) : a + b + c = a + (b + c) := by
  sorry


theorem commSemiring_add_comm (F : AlgebraFiltration k A)
    (a b : associatedGraded F) : a + b = b + a := by
  sorry



theorem commSemiring_nsmul_zero (F : AlgebraFiltration k A)
    (x : associatedGraded F) : nsmulRec 0 x = 0 := by
  sorry



theorem commSemiring_nsmul_succ (F : AlgebraFiltration k A)
    (n : ℕ) (x : associatedGraded F) :
    nsmulRec (n + 1) x = nsmulRec n x + x := by
  sorry


theorem commSemiring_left_distrib (F : AlgebraFiltration k A)
    (a b c : associatedGraded F) :
    mul F a (b + c) = mul F a b + mul F a c := by
  sorry


theorem commSemiring_right_distrib (F : AlgebraFiltration k A)
    (a b c : associatedGraded F) :
    mul F (a + b) c = mul F a c + mul F b c := by
  sorry


theorem commSemiring_zero_mul (F : AlgebraFiltration k A)
    (a : associatedGraded F) : mul F 0 a = 0 := by
  sorry


theorem commSemiring_mul_zero (F : AlgebraFiltration k A)
    (a : associatedGraded F) : mul F a 0 = 0 := by
  sorry


theorem commSemiring_mul_assoc (F : AlgebraFiltration k A)
    (a b c : associatedGraded F) :
    mul F (mul F a b) c = mul F a (mul F b c) := by
  sorry


theorem commSemiring_one_mul (F : AlgebraFiltration k A)
    (a : associatedGraded F) : mul F (one F) a = a := by
  sorry


theorem commSemiring_mul_one (F : AlgebraFiltration k A)
    (a : associatedGraded F) : mul F a (one F) = a := by
  sorry



theorem commSemiring_natCast_zero (F : AlgebraFiltration k A) :
    (Nat.recOn (motive := fun _ => associatedGraded F) 0 0
      (fun _ y => one F + y)) = 0 := by
  sorry



theorem commSemiring_natCast_succ (F : AlgebraFiltration k A) (n : ℕ) :
    (Nat.recOn (motive := fun _ => associatedGraded F) (n + 1) 0
        (fun _ y => one F + y))
      = (Nat.recOn (motive := fun _ => associatedGraded F) n 0
          (fun _ y => one F + y)) + one F := by
  sorry



theorem commSemiring_npow_zero (F : AlgebraFiltration k A)
    (x : associatedGraded F) :
    (Nat.recOn (motive := fun _ => associatedGraded F) 0 (one F)
      (fun _ y => mul F y x)) = one F := by
  sorry



theorem commSemiring_npow_succ (F : AlgebraFiltration k A)
    (n : ℕ) (x : associatedGraded F) :
    (Nat.recOn (motive := fun _ => associatedGraded F) (n + 1) (one F)
        (fun _ y => mul F y x))
      = mul F (Nat.recOn (motive := fun _ => associatedGraded F) n (one F)
          (fun _ y => mul F y x)) x := by
  sorry



theorem commSemiring_mul_comm (F : AlgebraFiltration k A)
    (a b : associatedGraded F) : mul F a b = mul F b a := by
  sorry










noncomputable instance commSemiring (F : AlgebraFiltration k A) :
    CommSemiring (associatedGraded F) where
  zero := 0
  add := (· + ·)
  nsmul := nsmulRec
  one := one F
  mul := mul F
  natCast := fun n => Nat.recOn n 0 (fun _ y => one F + y)
  npow := fun n x => Nat.recOn n (one F) (fun _ y => mul F y x)

  zero_add := commSemiring_zero_add F
  add_zero := commSemiring_add_zero F
  add_assoc := commSemiring_add_assoc F
  add_comm := commSemiring_add_comm F
  nsmul_zero := commSemiring_nsmul_zero F
  nsmul_succ := commSemiring_nsmul_succ F
  left_distrib := commSemiring_left_distrib F
  right_distrib := commSemiring_right_distrib F
  zero_mul := commSemiring_zero_mul F
  mul_zero := commSemiring_mul_zero F
  mul_assoc := commSemiring_mul_assoc F
  one_mul := commSemiring_one_mul F
  mul_one := commSemiring_mul_one F
  natCast_zero := commSemiring_natCast_zero F
  natCast_succ := commSemiring_natCast_succ F
  npow_zero := commSemiring_npow_zero F
  npow_succ := commSemiring_npow_succ F
  mul_comm := commSemiring_mul_comm F





theorem algebraMap_mem_zero
    (F : AlgebraFiltration k A) (r : k) :
    (algebraMap k A r) ∈ F.F 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (F.F 0).smul_mem r F.one_mem


def scalarClass
    (F : AlgebraFiltration k A) (r : k) :
    piece F 0 :=
  mk F 0 (algebraMap k A r) (algebraMap_mem_zero F r)


noncomputable def scalar
    (F : AlgebraFiltration k A) (r : k) :
    associatedGraded F :=
  ofPiece F 0 (scalarClass F r)

theorem degreeZeroRingHom_map_zero (F : AlgebraFiltration k A) :
    scalar F 0 = 0 := by
  sorry


theorem degreeZeroRingHom_map_one (F : AlgebraFiltration k A) :
    scalar F 1 = 1 := by
  sorry


theorem degreeZeroRingHom_map_add (F : AlgebraFiltration k A) (x y : k) :
    scalar F (x + y) = scalar F x + scalar F y := by
  sorry


theorem degreeZeroRingHom_map_mul (F : AlgebraFiltration k A) (x y : k) :
    scalar F (x * y) = scalar F x * scalar F y := by
  sorry





noncomputable def degreeZeroRingHom
    (F : AlgebraFiltration k A) :
    k →+* associatedGraded F where
  toFun := scalar F
  map_zero' := degreeZeroRingHom_map_zero F
  map_one' := degreeZeroRingHom_map_one F
  map_add' := degreeZeroRingHom_map_add F
  map_mul' := degreeZeroRingHom_map_mul F

theorem algebra_smul_def (F : AlgebraFiltration k A)
    (r : k) (x : associatedGraded F) :
    r • x = degreeZeroRingHom F r * x := by
  sorry





noncomputable instance algebra
    (F : AlgebraFiltration k A) :
    Algebra k (associatedGraded F) where
  smul := fun r x => r • x
  commutes' := by
        intro r x
        exact mul_comm _ _
  algebraMap := degreeZeroRingHom F
  smul_def' := algebra_smul_def F

end AssociatedGraded


theorem pbwFiltration_union_all
    (k : Type u) (L : Type v)
    [CommRing k] [LieRing L] [LieAlgebra k L] :
    ⋃ n : ℕ,
        (Submodule.span k
          {a : UniversalEnvelopingAlgebra k L |
            ∃ xs : List L, xs.length ≤ n ∧ a = ueaWord k L xs}).carrier = ⊤ := by
  sorry



theorem pbwFiltration_mul_mem
    (k : Type u) (L : Type v)
    [CommRing k] [LieRing L] [LieAlgebra k L]
    (i j : ℕ) (a b : UniversalEnvelopingAlgebra k L)
    (ha : a ∈ Submodule.span k
      {a : UniversalEnvelopingAlgebra k L |
        ∃ xs : List L, xs.length ≤ i ∧ a = ueaWord k L xs})
    (hb : b ∈ Submodule.span k
      {a : UniversalEnvelopingAlgebra k L |
        ∃ xs : List L, xs.length ≤ j ∧ a = ueaWord k L xs}) :
    a * b ∈ Submodule.span k
      {a : UniversalEnvelopingAlgebra k L |
        ∃ xs : List L, xs.length ≤ i + j ∧ a = ueaWord k L xs} := by
  
  
  
  sorry



theorem pbwFiltration_commutator_mem_lower
    (k : Type u) (L : Type v)
    [CommRing k] [LieRing L] [LieAlgebra k L]
    (i j : ℕ) (a b : UniversalEnvelopingAlgebra k L)
    (ha : a ∈ Submodule.span k
      {a : UniversalEnvelopingAlgebra k L |
        ∃ xs : List L, xs.length ≤ i ∧ a = ueaWord k L xs})
    (hb : b ∈ Submodule.span k
      {a : UniversalEnvelopingAlgebra k L |
        ∃ xs : List L, xs.length ≤ j ∧ a = ueaWord k L xs}) :
    a * b - b * a ∈
      match i + j with
      | 0 => ⊥
      | n + 1 =>
        Submodule.span k
          {a : UniversalEnvelopingAlgebra k L |
            ∃ xs : List L, xs.length ≤ n ∧ a = ueaWord k L xs} := by
  
  
  
  
  
  sorry







noncomputable def pbwFiltration
    (k : Type u) (L : Type v)
    [CommRing k] [LieRing L] [LieAlgebra k L] :
    AlgebraFiltration k (UniversalEnvelopingAlgebra k L) where
  F n :=
    Submodule.span k
      {a : UniversalEnvelopingAlgebra k L |
        ∃ xs : List L, xs.length ≤ n ∧ a = ueaWord k L xs}
  mono := by
    intro i j hij a ha
    refine Submodule.span_mono ?_ ha
    intro a ha
    rcases ha with ⟨xs, hxs, rfl⟩
    exact ⟨xs, le_trans hxs hij, rfl⟩
  one_mem := by
    apply Submodule.subset_span
    exact ⟨[], by simp, rfl⟩
  union_all := pbwFiltration_union_all k L
  mul_mem := fun {i j a b} ha hb => pbwFiltration_mul_mem k L i j a b ha hb
  commutator_mem_lower := fun {i j a b} ha hb =>
    pbwFiltration_commutator_mem_lower k L i j a b ha hb

noncomputable def pbwDegreeOne
    (k : Type u) (L : Type v)
    [Field k] [LieRing L] [LieAlgebra k L] :
    L → associatedGraded (pbwFiltration k L) :=
  fun x =>
    ofPiece (pbwFiltration k L)
      1
      (mk
        (pbwFiltration k L)
        1
        (UniversalEnvelopingAlgebra.ι k x)
        (by
          apply Submodule.subset_span
          exact ⟨[x], by simp, by simp [ueaWord]⟩))



theorem pbwMap_degreeOne_map_add
    (k : Type u) (L : Type v)
    [Field k] [LieRing L] [LieAlgebra k L]
    (x y : L) :
    ofPiece (pbwFiltration k L) 1
        (mk (pbwFiltration k L) 1 (UniversalEnvelopingAlgebra.ι k (x + y))
          (by
            apply Submodule.subset_span
            exact ⟨[x + y], by simp, by simp [ueaWord]⟩))
      = ofPiece (pbwFiltration k L) 1
          (mk (pbwFiltration k L) 1 (UniversalEnvelopingAlgebra.ι k x)
            (by
              apply Submodule.subset_span
              exact ⟨[x], by simp, by simp [ueaWord]⟩))
        + ofPiece (pbwFiltration k L) 1
          (mk (pbwFiltration k L) 1 (UniversalEnvelopingAlgebra.ι k y)
            (by
              apply Submodule.subset_span
              exact ⟨[y], by simp, by simp [ueaWord]⟩)) := by
  
  
  sorry



theorem pbwMap_degreeOne_map_smul
    (k : Type u) (L : Type v)
    [Field k] [LieRing L] [LieAlgebra k L]
    (r : k) (x : L) :
    ofPiece (pbwFiltration k L) 1
        (mk (pbwFiltration k L) 1 (UniversalEnvelopingAlgebra.ι k (r • x))
          (by
            apply Submodule.subset_span
            exact ⟨[r • x], by simp, by simp [ueaWord]⟩))
      = (RingHom.id k) r •
          ofPiece (pbwFiltration k L) 1
            (mk (pbwFiltration k L) 1 (UniversalEnvelopingAlgebra.ι k x)
              (by
                apply Submodule.subset_span
                exact ⟨[x], by simp, by simp [ueaWord]⟩)) := by
  
  
  sorry







noncomputable def pbwMap
    (k : Type u) (L : Type v)
    [Field k] [LieRing L] [LieAlgebra k L] :
    SymmetricAlgebra k L →ₐ[k] associatedGraded (pbwFiltration k L) := by
  classical

  let F : AlgebraFiltration k (UniversalEnvelopingAlgebra k L) :=
    pbwFiltration k L

  
  
  
  letI : CommSemiring (associatedGraded F) :=
    commSemiring F

  letI : AddCommMonoid (associatedGraded F) :=
    (inferInstance : CommSemiring (associatedGraded F)).toNonAssocSemiring.toAddCommMonoid

  letI : Algebra k (associatedGraded F) :=
    algebra F

  letI : Module k (associatedGraded F) :=
    (Algebra.toModule : Module k (associatedGraded F))

  refine
    (SymmetricAlgebra.lift
      (R := k)
      (M := L)
      (A := associatedGraded F)) ?degreeOneMap

  exact
    ({
      toFun := fun x =>
        (ofPiece F 1
          (mk
            F
            1
            (UniversalEnvelopingAlgebra.ι k x)
            (by
              apply Submodule.subset_span
              exact ⟨[x], by simp, by simp [ueaWord]⟩))
          : associatedGraded F)

      map_add' := pbwMap_degreeOne_map_add k L

      map_smul' := pbwMap_degreeOne_map_smul k L
    } : L →ₗ[k] associatedGraded F)






theorem theorem_13_1_poincare_birkhoff_witt
    (k : Type u) (L : Type v)
    [Field k] [LieRing L] [LieAlgebra k L] :
    Function.Bijective (pbwMap k L) := by
  sorry

end Autoform_Lie_groups_lie_algebras_lie_theorem_13_1_poincare_birkhoff_witt
