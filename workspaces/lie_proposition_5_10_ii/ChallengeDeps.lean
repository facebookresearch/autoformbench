import Mathlib

open scoped TensorProduct

namespace Autoform_Lie_groups_lie_algebras_lie_proposition_5_10_ii

universe u𝕜 uE uH uG uF uB

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]

variable {E : Type uE}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable [FiniteDimensional 𝕜 E]

variable {H : Type uH} [TopologicalSpace H]
variable (I : ModelWithCorners 𝕜 E H)

variable {G : Type uG}
variable [TopologicalSpace G] [ChartedSpace H G] [Group G]
variable [IsManifold I (⊤ : WithTop ℕ∞) G]
variable [LieGroup I (⊤ : WithTop ℕ∞) G]













abbrev TensorType (k m : ℕ) (V : Type*)
    [AddCommGroup V] [Module 𝕜 V] : Type _ :=
  TensorProduct 𝕜
    (TensorPower 𝕜 k V)
    (TensorPower 𝕜 m (Module.Dual 𝕜 V))


abbrev TensorModel (k m : ℕ) : Type _ :=
  TensorType (𝕜 := 𝕜) k m E


abbrev TensorFiberAt (k m : ℕ) (g : G) : Type _ :=
  TensorType (𝕜 := 𝕜) k m (TangentSpace I g)







abbrev LieTensor (k m : ℕ) : Type _ :=
  TensorType (𝕜 := 𝕜) k m (GroupLieAlgebra I G)


noncomputable def tensorPowerMap {V W : Type*}
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W]
    (n : ℕ) (f : V →ₗ[𝕜] W) :
    TensorPower 𝕜 n V →ₗ[𝕜] TensorPower 𝕜 n W :=
  PiTensorProduct.map
    (R := 𝕜)
    (s := fun _ : Fin n => V)
    (t := fun _ : Fin n => W)
    (fun _ => f)






noncomputable def dualPush {V W : Type*}
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W]
    (fInv : W →ₗ[𝕜] V) :
    Module.Dual 𝕜 V →ₗ[𝕜] Module.Dual 𝕜 W :=
  fInv.dualMap






noncomputable def transportTensor {V W : Type*}
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W]
    (k m : ℕ) (f : V →ₗ[𝕜] W) (fInv : W →ₗ[𝕜] V) :
    TensorType (𝕜 := 𝕜) k m V →ₗ[𝕜]
      TensorType (𝕜 := 𝕜) k m W :=
  TensorProduct.map
    (tensorPowerMap (𝕜 := 𝕜) k f)
    (tensorPowerMap (𝕜 := 𝕜) m (dualPush (𝕜 := 𝕜) fInv))








def leftTranslation (q x : G) : G :=
  q * x



def rightTranslation (q x : G) : G :=
  x * q⁻¹















section BundleInterface

variable {F : Type uF}
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {B : G → Type uB}
variable [TopologicalSpace (Bundle.TotalSpace F B)]
variable [(g : G) → TopologicalSpace (B g)]
variable [FiberBundle F B]
variable [(g : G) → AddCommGroup (B g)]
variable [(g : G) → Module 𝕜 (B g)]
variable [VectorBundle 𝕜 F B]
variable [ContMDiffVectorBundle (⊤ : WithTop ℕ∞) F B I]


noncomputable def castFiber {x y : G} (h : x = y) :
    B x →ₗ[𝕜] B y := by
  subst h
  exact LinearMap.id






abbrev SmoothTensorField : Type _ :=
  ContMDiffSection I F (⊤ : WithTop ℕ∞) B















structure IsMixedTensorBundle (k m : ℕ) : Type _ where
  
  fiberEquiv :
    ∀ g : G, B g ≃ₗ[𝕜] TensorFiberAt (𝕜 := 𝕜) (I := I) k m g

  
  modelFiberEquiv :
    F ≃ₗ[𝕜] TensorModel (𝕜 := 𝕜) (E := E) k m

  
  localTriv :
    G →
      Bundle.Trivialization F
        (Bundle.TotalSpace.proj : Bundle.TotalSpace F B → G)

  
  localTriv_linear :
    ∀ g₀ : G, Bundle.Trivialization.IsLinear 𝕜 (localTriv g₀)

  
  localTriv_mem_base :
    ∀ g₀ : G, g₀ ∈ (localTriv g₀).baseSet

  




  tangentCoord :
    ∀ g₀ x : G, x ∈ (localTriv g₀).baseSet →
      TangentSpace I x ≃ₗ[𝕜] E

  




  localTriv_tensor_coord :
    ∀ g₀ x : G, ∀ hx : x ∈ (localTriv g₀).baseSet,
      letI : Bundle.Trivialization.IsLinear 𝕜 (localTriv g₀) :=
        localTriv_linear g₀
      modelFiberEquiv.toLinearMap.comp
          (Bundle.Trivialization.linearMapAt 𝕜 (localTriv g₀) x)
      =
      (transportTensor (𝕜 := 𝕜) k m
          (tangentCoord g₀ x hx).toLinearMap
          (tangentCoord g₀ x hx).symm.toLinearMap).comp
        (fiberEquiv x).toLinearMap

  



  dLeft :
    ∀ q x : G,
      TangentSpace I x ≃ₗ[𝕜] TangentSpace I (leftTranslation q x)

  

  dRight :
    ∀ q x : G,
      TangentSpace I x ≃ₗ[𝕜] TangentSpace I (rightTranslation q x)

  
  dAd :
    G →
      GroupLieAlgebra I G ≃ₗ[𝕜] GroupLieAlgebra I G

  
  leftTransport :
    ∀ q x : G, B x ≃ₗ[𝕜] B (leftTranslation q x)

  
  rightTransport :
    ∀ q x : G, B x ≃ₗ[𝕜] B (rightTranslation q x)

  
  adTransportAtOne :
    G → B (1 : G) ≃ₗ[𝕜] B (1 : G)

  

  leftTransport_fiber_eq :
    ∀ (q x : G) (t : TensorFiberAt (𝕜 := 𝕜) (I := I) k m x),
      fiberEquiv (leftTranslation q x)
        ((leftTransport q x) ((fiberEquiv x).symm t))
      =
      transportTensor (𝕜 := 𝕜) k m
        (dLeft q x).toLinearMap
        (dLeft q x).symm.toLinearMap
        t

  

  rightTransport_fiber_eq :
    ∀ (q x : G) (t : TensorFiberAt (𝕜 := 𝕜) (I := I) k m x),
      fiberEquiv (rightTranslation q x)
        ((rightTransport q x) ((fiberEquiv x).symm t))
      =
      transportTensor (𝕜 := 𝕜) k m
        (dRight q x).toLinearMap
        (dRight q x).symm.toLinearMap
        t

  

  adTransport_fiber_eq :
    ∀ (q : G) (τ : LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m),
      fiberEquiv 1
        ((adTransportAtOne q) ((fiberEquiv 1).symm τ))
      =
      transportTensor (𝕜 := 𝕜) k m
        (dAd q).toLinearMap
        (dAd q).symm.toLinearMap
        τ

  
  leftTransport_one :
    ∀ (x : G) (b : B x),
      castFiber (𝕜 := 𝕜) (B := B)
        (by simp [leftTranslation] : leftTranslation (1 : G) x = x)
        ((leftTransport (1 : G) x) b)
      =
      b

  
  leftTransport_mul :
    ∀ (q r x : G) (b : B x),
      castFiber (𝕜 := 𝕜) (B := B)
        (by
          simp [leftTranslation, mul_assoc] :
            leftTranslation q (leftTranslation r x) =
              leftTranslation (q * r) x)
        ((leftTransport q (leftTranslation r x))
          ((leftTransport r x) b))
      =
      (leftTransport (q * r) x) b

  
  rightTransport_one :
    ∀ (x : G) (b : B x),
      castFiber (𝕜 := 𝕜) (B := B)
        (by simp [rightTranslation] : rightTranslation (1 : G) x = x)
        ((rightTransport (1 : G) x) b)
      =
      b

  



  rightTransport_mul :
    ∀ (q r x : G) (b : B x),
      castFiber (𝕜 := 𝕜) (B := B)
        (by
          simp [rightTranslation, mul_assoc] :
            rightTranslation q (rightTranslation r x) =
              rightTranslation (q * r) x)
        ((rightTransport q (rightTranslation r x))
          ((rightTransport r x) b))
      =
      (rightTransport (q * r) x) b

  




  left_rightTransport_commute :
    ∀ (q r x : G) (b : B x),
      castFiber (𝕜 := 𝕜) (B := B)
        (by
          simp [leftTranslation, rightTranslation, mul_assoc] :
            rightTranslation r (leftTranslation q x) =
              leftTranslation q (rightTranslation r x))
        ((rightTransport r (leftTranslation q x))
          ((leftTransport q x) b))
      =
      (leftTransport q (rightTranslation r x))
        ((rightTransport r x) b)

  



  adTransport_eq_right_left :
    ∀ (q : G) (b : B (1 : G)),
      castFiber (𝕜 := 𝕜) (B := B)
        (by
          simp [leftTranslation, rightTranslation] :
            rightTranslation q (leftTranslation q (1 : G)) = 1)
        ((rightTransport q (leftTranslation q (1 : G)))
          ((leftTransport q (1 : G)) b))
      =
      (adTransportAtOne q) b

  
  adTransport_one :
    ∀ b : B (1 : G),
      (adTransportAtOne (1 : G)) b = b

  
  adTransport_mul :
    ∀ (q r : G) (b : B (1 : G)),
      (adTransportAtOne q) ((adTransportAtOne r) b)
      =
      (adTransportAtOne (q * r)) b

  



  leftExtension :
    LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m →
      SmoothTensorField (I := I) (B := B) (F := F)

  
  leftExtension_apply :
    ∀ (τ : LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m) (g : G),
      leftExtension τ g =
        castFiber (𝕜 := 𝕜) (B := B)
          (by simp [leftTranslation] :
            leftTranslation g (1 : G) = g)
          ((leftTransport g (1 : G)) ((fiberEquiv 1).symm τ))

  



  rightExtension :
    LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m →
      SmoothTensorField (I := I) (B := B) (F := F)

  
  rightExtension_apply :
    ∀ (τ : LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m) (g : G),
      rightExtension τ g =
        castFiber (𝕜 := 𝕜) (B := B)
          (by
            simp [rightTranslation] :
              rightTranslation g⁻¹ (1 : G) = g)
          ((rightTransport g⁻¹ (1 : G)) ((fiberEquiv 1).symm τ))

variable {k m : ℕ}
variable (MT : IsMixedTensorBundle (𝕜 := 𝕜) (I := I) (B := B) (F := F) k m)



noncomputable def valueAtOne
    (T : SmoothTensorField (I := I) (B := B) (F := F)) :
    LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m :=
  MT.fiberEquiv 1 (T 1)


def IsLeftInvariant
    (T : SmoothTensorField (I := I) (B := B) (F := F)) : Prop :=
  ∀ q x : G,
    (MT.leftTransport q x) (T x) =
      T (leftTranslation q x)



def IsRightInvariant
    (T : SmoothTensorField (I := I) (B := B) (F := F)) : Prop :=
  ∀ q x : G,
    (MT.rightTransport q x) (T x) =
      T (rightTranslation q x)



noncomputable def tensorAdAction (q : G) :
    LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m →ₗ[𝕜]
      LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m :=
  (MT.fiberEquiv 1).toLinearMap.comp
    ((MT.adTransportAtOne q).toLinearMap.comp
      (MT.fiberEquiv 1).symm.toLinearMap)


def IsAdInvariant
    (τ : LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m) : Prop :=
  ∀ q : G,
    tensorAdAction (𝕜 := 𝕜) (I := I) (B := B) (F := F) MT q τ = τ


noncomputable def leftInvariantExtension
    (τ : LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m) :
    SmoothTensorField (I := I) (B := B) (F := F) :=
  MT.leftExtension τ




noncomputable def rightInvariantExtension
    (τ : LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m) :
    SmoothTensorField (I := I) (B := B) (F := F) :=
  MT.rightExtension τ







































end BundleInterface

end Autoform_Lie_groups_lie_algebras_lie_proposition_5_10_ii
