import Mathlib






















universe u v w

namespace Autoform_Noncommutative_Algebra_noncomm_alg_proposition_8_5_universal

noncomputable section








def commutatorAddSubgroup (R : Type u) [Ring R] : AddSubgroup R :=
  AddSubgroup.closure {x : R | ∃ a b : R, x = a * b - b * a}







abbrev Cocenter (R : Type u) [Ring R] : Type u :=
  R ⧸ commutatorAddSubgroup R








structure FgProjectiveModule (R : Type u) [Ring R] where
  carrier : Type u
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]
  [isFinite : Module.Finite R carrier]
  [isProjective : Module.Projective R carrier]

attribute [instance] FgProjectiveModule.isAddCommGroup
attribute [instance] FgProjectiveModule.isModule
attribute [instance] FgProjectiveModule.isFinite
attribute [instance] FgProjectiveModule.isProjective





def prodLinearEnd
    {R : Type u} [Ring R]
    {P Q : Type u}
    [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    (φ : P →ₗ[R] P) (ψ : Q →ₗ[R] Q) :
    P × Q →ₗ[R] P × Q where
  toFun x := (φ x.1, ψ x.2)
  map_add' x y := by
    ext <;> simp
  map_smul' r x := by
    ext <;> simp














structure TraceMap
    (R : Type u) [Ring R]
    (A : Type v) [AddCommGroup A] where
  trace :
    (P : FgProjectiveModule R) →
      (P.carrier →ₗ[R] P.carrier) → A
  map_add :
    ∀ (P : FgProjectiveModule R)
      (φ ψ : P.carrier →ₗ[R] P.carrier),
        trace P (φ + ψ) = trace P φ + trace P ψ
  map_directSum :
    ∀ (P Q Z : FgProjectiveModule R)
      (e : Z.carrier ≃ₗ[R] P.carrier × Q.carrier)
      (φ : P.carrier →ₗ[R] P.carrier)
      (ψ : Q.carrier →ₗ[R] Q.carrier)
      (χ : Z.carrier →ₗ[R] Z.carrier),
        e.toLinearMap.comp χ =
            (prodLinearEnd φ ψ).comp e.toLinearMap →
          trace Z χ = trace P φ + trace Q ψ
  map_cyclic :
    ∀ (P Q : FgProjectiveModule R)
      (a : Q.carrier →ₗ[R] P.carrier)
      (b : P.carrier →ₗ[R] Q.carrier),
        trace P (a.comp b) = trace Q (b.comp a)








def IsUniversalTraceTarget
    (R : Type u) [Ring R]
    (U : Type v) [AddCommGroup U]
    (τ : TraceMap R U) : Prop :=
  ∀ (A : Type w) [AddCommGroup A] (σ : TraceMap R A),
    ∃! f : U →+ A,
      ∀ (P : FgProjectiveModule R)
        (φ : P.carrier →ₗ[R] P.carrier),
          f (τ.trace P φ) = σ.trace P φ





structure TraceGenerator (R : Type u) [Ring R] where
  projective : FgProjectiveModule R
  endomorphism : projective.carrier →ₗ[R] projective.carrier







abbrev TraceFreeAbelianGroup (R : Type u) [Ring R] : Type (u + 1) :=
  TraceGenerator R →₀ ℤ




def traceGeneratorElement
    {R : Type u} [Ring R]
    (P : FgProjectiveModule R)
    (φ : P.carrier →ₗ[R] P.carrier) :
    TraceFreeAbelianGroup R := by
  classical
  exact
    Finsupp.single
      ({ projective := P, endomorphism := φ } : TraceGenerator R)
      (1 : ℤ)










inductive TraceRelationIndex (R : Type u) [Ring R] : Type (u + 1)
  | endomorphismAdd
      (P : FgProjectiveModule R)
      (φ ψ : P.carrier →ₗ[R] P.carrier)
  | directSum
      (P Q Z : FgProjectiveModule R)
      (e : Z.carrier ≃ₗ[R] P.carrier × Q.carrier)
      (φ : P.carrier →ₗ[R] P.carrier)
      (ψ : Q.carrier →ₗ[R] Q.carrier)
      (χ : Z.carrier →ₗ[R] Z.carrier)
      (compat :
        e.toLinearMap.comp χ =
          (prodLinearEnd φ ψ).comp e.toLinearMap)
  | cyclic
      (P Q : FgProjectiveModule R)
      (a : Q.carrier →ₗ[R] P.carrier)
      (b : P.carrier →ₗ[R] Q.carrier)




def traceRelationElement
    {R : Type u} [Ring R] :
    TraceRelationIndex R → TraceFreeAbelianGroup R
  | TraceRelationIndex.endomorphismAdd P φ ψ =>
      traceGeneratorElement P (φ + ψ)
        - traceGeneratorElement P φ
        - traceGeneratorElement P ψ
  | TraceRelationIndex.directSum P Q Z _ φ ψ χ _ =>
      traceGeneratorElement Z χ
        - traceGeneratorElement P φ
        - traceGeneratorElement Q ψ
  | TraceRelationIndex.cyclic P Q a b =>
      traceGeneratorElement P (a.comp b)
        - traceGeneratorElement Q (b.comp a)





def traceRelationSubgroup
    (R : Type u) [Ring R] :
    AddSubgroup (TraceFreeAbelianGroup R) :=
  AddSubgroup.closure (Set.range (traceRelationElement (R := R)))





abbrev PresentedTraceGroup (R : Type u) [Ring R] : Type (u + 1) :=
  TraceFreeAbelianGroup R ⧸ traceRelationSubgroup R





end

end Autoform_Noncommutative_Algebra_noncomm_alg_proposition_8_5_universal
