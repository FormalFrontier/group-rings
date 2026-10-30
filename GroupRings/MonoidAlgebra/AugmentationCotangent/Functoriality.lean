/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.AugmentationCotangent.Tensor
public import GroupRings.MonoidAlgebra.CoefficientChange
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Coefficient covariance, tensor naturality and product splitting

Coefficient changes use the universal property with canonical restriction of scalars.
The group comparison is natural for these arrows. Binary monoid products split.
The tensor arrow is the tensor product over the integers of the two additive maps.
-/

@[expose] public section

universe u v w u₁

open scoped TensorProduct

namespace MonoidAlgebra

variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable (M : Type w) [Monoid M]

/-- Coefficient covariance, semilinear for the coefficient ring homomorphism. -/
noncomputable def augmentationCotangentCoeffMap (f : R →+* S) :
    AugmentationCotangent R M →ₛₗ[f] AugmentationCotangent S M := by
  let : Module R (AugmentationCotangent S M) :=
    Module.compHom (AugmentationCotangent S M) f
  let L := augmentationCotangentLift R M (augmentationCotangentDeltaHom S M)
  exact {
    toFun := L
    map_add' := L.map_add
    map_smul' := fun r x => L.map_smul r x }

/-- A coefficient change fixes the monoid-labelled generator. -/
@[simp] theorem augmentationCotangentCoeffMap_delta (f : R →+* S) (m : M) :
    augmentationCotangentCoeffMap M f (augmentationCotangentDelta R M m) =
      augmentationCotangentDelta S M m := by
  let : Module R (AugmentationCotangent S M) :=
    Module.compHom (AugmentationCotangent S M) f
  exact augmentationCotangentLift_delta R M (augmentationCotangentDeltaHom S M) m

/-- The coefficient change on a full augmentation element, as a coefficient sum. -/
theorem augmentationCotangentCoeffMap_toAugmentationCotangent_sum
    (f : R →+* S) (x : RingHom.ker (augmentation R M)) :
    augmentationCotangentCoeffMap M f (toAugmentationCotangent R M x) =
      (x : MonoidAlgebra R M).coeff.sum
        (fun m r => f r • augmentationCotangentDelta S M m) := by
  let : Module R (AugmentationCotangent S M) :=
    Module.compHom (AugmentationCotangent S M) f
  exact augmentationCotangentLift_toAugmentationCotangent R M
    (augmentationCotangentDeltaHom S M) x

variable {N : Type u₁} [Monoid N]

/-- Simultaneous coefficient and monoid covariance. -/
noncomputable def augmentationCotangentMapRingHom
    (f : R →+* S) (φ : M →* N) :
    AugmentationCotangent R M →ₛₗ[f] AugmentationCotangent S N :=
  (augmentationCotangentMap S M φ).comp (augmentationCotangentCoeffMap M f)

/-- The combined arrow is coefficient change followed by monoid covariance. -/
theorem augmentationCotangentMapRingHom_apply
    (f : R →+* S) (φ : M →* N) (x : AugmentationCotangent R M) :
    augmentationCotangentMapRingHom M f φ x =
      augmentationCotangentMap S M φ (augmentationCotangentCoeffMap M f x) := rfl

section Groups

variable {G : Type w} {H : Type u₁} [Group G] [Group H]

/-- The integer tensor of coefficient change and the induced abelianization map. -/
noncomputable def augmentationCotangentTensorMap (f : R →+* S) (φ : G →* H) :
    R ⊗[ℤ] Additive (Abelianization G) →ₗ[ℤ]
      S ⊗[ℤ] Additive (Abelianization H) :=
  TensorProduct.map f.toAddMonoidHom.toIntLinearMap
    (Abelianization.map φ).toAdditive.toIntLinearMap

/-- Formula for the tensor arrow on every pure tensor. -/
@[simp] theorem augmentationCotangentTensorMap_tmul
    (f : R →+* S) (φ : G →* H) (r : R) (a : Additive (Abelianization G)) :
    augmentationCotangentTensorMap f φ (r ⊗ₜ[ℤ] a) =
      f r ⊗ₜ[ℤ] Additive.ofMul (Abelianization.map φ a.toMul) := by
  exact TensorProduct.map_tmul _ _ r a

/-- The integer tensor arrow is semilinear for the full coefficient-left actions. -/
theorem augmentationCotangentTensorMap_smul
    (f : R →+* S) (φ : G →* H) (r : R)
    (x : R ⊗[ℤ] Additive (Abelianization G)) :
    augmentationCotangentTensorMap f φ (r • x) =
      f r • augmentationCotangentTensorMap f φ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simp [TensorProduct.smul_tmul', map_mul]
  | add x y hx hy =>
    simp only [smul_add, map_add, hx, hy]

end Groups

/-- Projection to the two cotangent factors, for arbitrary monoids. -/
noncomputable def augmentationCotangentProdMap :
    AugmentationCotangent R (M × N) →ₗ[R]
      AugmentationCotangent R M × AugmentationCotangent R N :=
  (augmentationCotangentMap R (M × N) (MonoidHom.fst M N)).prod
    (augmentationCotangentMap R (M × N) (MonoidHom.snd M N))

/-- The inclusion-sum arrow from the pair of cotangent factors. -/
noncomputable def augmentationCotangentProdInv :
    (AugmentationCotangent R M × AugmentationCotangent R N) →ₗ[R]
      AugmentationCotangent R (M × N) :=
  (augmentationCotangentMap R M (MonoidHom.inl M N)).coprod
    (augmentationCotangentMap R N (MonoidHom.inr M N))

/-- Projection formula for the product arrow. -/
theorem augmentationCotangentProdMap_apply (x : AugmentationCotangent R (M × N)) :
    augmentationCotangentProdMap M x =
      (augmentationCotangentMap R (M × N) (MonoidHom.fst M N) x,
        augmentationCotangentMap R (M × N) (MonoidHom.snd M N) x) := rfl

/-- The inclusion-sum arrow is the sum of the two inclusion maps. -/
theorem augmentationCotangentProdInv_apply
    (x : AugmentationCotangent R M) (y : AugmentationCotangent R N) :
    augmentationCotangentProdInv M (x, y) =
      augmentationCotangentMap R M (MonoidHom.inl M N) x +
        augmentationCotangentMap R N (MonoidHom.inr M N) y := rfl


/-- Coefficient covariance respects the coefficient-left action on every class. -/
theorem augmentationCotangentCoeffMap_smul (f : R →+* S) (r : R)
    (x : AugmentationCotangent R M) :
    augmentationCotangentCoeffMap M f (r • x) =
      f r • augmentationCotangentCoeffMap M f x :=
  (augmentationCotangentCoeffMap M f).map_smulₛₗ r x

/-- A scalar multiple of a delta class changes its coefficient by `f`. -/
theorem augmentationCotangentCoeffMap_smul_delta
    (f : R →+* S) (r : R) (m : M) :
    augmentationCotangentCoeffMap M f (r • augmentationCotangentDelta R M m) =
      f r • augmentationCotangentDelta S M m := by simp

/-- Coefficient covariance sends the class of an augmentation element to its image. -/
theorem augmentationCotangentCoeffMap_toAugmentationCotangent
    (f : R →+* S) (x : RingHom.ker (augmentation R M)) :
    augmentationCotangentCoeffMap M f (toAugmentationCotangent R M x) =
      toAugmentationCotangent S M ⟨mapRingHom M f x, by
        change augmentation S M (mapRingHom M f x) = 0
        rw [augmentation_mapRingHom, x.property, map_zero]⟩ := by
  let : Module R (AugmentationCotangent S M) :=
    Module.compHom (AugmentationCotangent S M) f
  have hs (r : R) (z : AugmentationCotangent S M) : r • z = f r • z := rfl
  have h (y : MonoidAlgebra R M) :
      augmentationCharacterLinearMap R M (augmentationCotangentDeltaHom S M) y =
        augmentationCharacterLinearMap S M (augmentationCotangentDeltaHom S M)
          (mapRingHom M f y) := by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single m r => simp only [mapRingHom_single, augmentationCharacterLinearMap_single]; rfl
  rw [augmentationCotangentCoeffMap_toAugmentationCotangent_sum,
    toAugmentationCotangent_eq_sum]
  simpa only [augmentationCharacterLinearMap_apply,
    augmentationCotangentDeltaHom_apply, hs] using h (x : MonoidAlgebra R M)

/-- Identity coefficients induce the identity map. -/
@[simp] theorem augmentationCotangentCoeffMap_id :
    augmentationCotangentCoeffMap M (RingHom.id R) = LinearMap.id := by
  apply augmentationCotangent_semilinearMap_ext R M
  intro m
  simp

/-- Coefficient changes compose on every cotangent class. -/
theorem augmentationCotangentCoeffMap_comp
    {T : Type*} [Ring T] (f : R →+* S) (g : S →+* T)
    (x : AugmentationCotangent R M) :
    augmentationCotangentCoeffMap M (g.comp f) x =
      augmentationCotangentCoeffMap M g (augmentationCotangentCoeffMap M f x) := by
  let : RingHomCompTriple f g (g.comp f) := ⟨rfl⟩
  have h : augmentationCotangentCoeffMap M (g.comp f) =
      LinearMap.comp (σ₁₃ := g.comp f)
        (augmentationCotangentCoeffMap M g) (augmentationCotangentCoeffMap M f) := by
    apply augmentationCotangent_semilinearMap_ext R M
    intro m
    simp
  exact DFunLike.congr_fun h x

/-- The combined arrow sends each delta class to the image-labelled delta class. -/
@[simp] theorem augmentationCotangentMapRingHom_delta
    (f : R →+* S) (φ : M →* N) (m : M) :
    augmentationCotangentMapRingHom M f φ (augmentationCotangentDelta R M m) =
      augmentationCotangentDelta S N (φ m) := by
  simp [augmentationCotangentMapRingHom_apply]

/-- Coefficient and monoid covariance commute. -/
theorem augmentationCotangentMapRingHom_eq_coeffMap_comp
    (f : R →+* S) (φ : M →* N) :
    augmentationCotangentMapRingHom M f φ =
      (augmentationCotangentCoeffMap N f).comp (augmentationCotangentMap R M φ) := by
  apply augmentationCotangent_semilinearMap_ext R M
  intro m
  simp

/-- The other order of the commuting coefficient/monoid square, pointwise. -/
theorem augmentationCotangentCoeffMap_map
    (f : R →+* S) (φ : M →* N) (x : AugmentationCotangent R M) :
    augmentationCotangentCoeffMap N f (augmentationCotangentMap R M φ x) =
      augmentationCotangentMap S M φ (augmentationCotangentCoeffMap M f x) :=
  (DFunLike.congr_fun (augmentationCotangentMapRingHom_eq_coeffMap_comp M f φ) x).symm

/-- Monoid covariance on the class of every augmentation element. -/
theorem augmentationCotangentMap_toAugmentationCotangent_image
    (φ : M →* N) (x : RingHom.ker (augmentation R M)) :
    augmentationCotangentMap R M φ (toAugmentationCotangent R M x) =
      toAugmentationCotangent R N ⟨mapDomainRingHom R φ x, by
        exact (DFunLike.congr_fun (augmentation_comp_mapDomainRingHom R M φ)
          (x : MonoidAlgebra R M)).trans x.property⟩ := by
  have h (y : MonoidAlgebra R M) :
      augmentationCharacterLinearMap R M ((augmentationCotangentDeltaHom R N).comp φ) y =
        augmentationCharacterLinearMap R N (augmentationCotangentDeltaHom R N)
          (mapDomainRingHom R φ y) := by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single m r => simp [augmentationCharacterLinearMap_single]
  rw [augmentationCotangentMap_toAugmentationCotangent, toAugmentationCotangent_eq_sum]
  simpa only [augmentationCharacterLinearMap_apply, MonoidHom.comp_apply,
    augmentationCotangentDeltaHom_apply] using h (x : MonoidAlgebra R M)

/-- The combined arrow is the class of the full coefficient and monoid image. -/
theorem augmentationCotangentMapRingHom_toAugmentationCotangent
    (f : R →+* S) (φ : M →* N) (x : RingHom.ker (augmentation R M)) :
    augmentationCotangentMapRingHom M f φ (toAugmentationCotangent R M x) =
      toAugmentationCotangent S N
        ⟨mapDomainRingHom S φ (mapRingHom M f x), by
          rw [RingHom.mem_ker,
            ← RingHom.comp_apply (augmentation S N) (mapDomainRingHom S φ),
            augmentation_comp_mapDomainRingHom,
            augmentation_mapRingHom, x.property, map_zero]⟩ := by
  rw [augmentationCotangentMapRingHom_apply,
    augmentationCotangentCoeffMap_toAugmentationCotangent,
    augmentationCotangentMap_toAugmentationCotangent_image]

/-- Identity coefficients recover the fixed-coefficient monoid map. -/
@[simp] theorem augmentationCotangentMapRingHom_id_coeff (φ : M →* N) :
    augmentationCotangentMapRingHom M (RingHom.id R) φ = augmentationCotangentMap R M φ := by
  apply augmentationCotangent_linearMap_ext R M
  intro m
  simp

/-- Identity monoid covariance recovers coefficient covariance. -/
@[simp] theorem augmentationCotangentMapRingHom_id_monoid (f : R →+* S) :
    augmentationCotangentMapRingHom M f (MonoidHom.id M) =
      augmentationCotangentCoeffMap M f := by
  apply augmentationCotangent_semilinearMap_ext R M
  intro m
  simp

/-- The combined identity arrow is the identity. -/
theorem augmentationCotangentMapRingHom_id :
    augmentationCotangentMapRingHom M (RingHom.id R) (MonoidHom.id M) = LinearMap.id := by
  simp

/-- Combined covariance respects composition in both variables. -/
theorem augmentationCotangentMapRingHom_comp
    {T : Type*} [Ring T] {P : Type*} [Monoid P]
    (f : R →+* S) (g : S →+* T) (φ : M →* N) (ψ : N →* P)
    (x : AugmentationCotangent R M) :
    augmentationCotangentMapRingHom M (g.comp f) (ψ.comp φ) x =
      augmentationCotangentMapRingHom N g ψ (augmentationCotangentMapRingHom M f φ x) := by
  let : RingHomCompTriple f g (g.comp f) := ⟨rfl⟩
  have h : augmentationCotangentMapRingHom M (g.comp f) (ψ.comp φ) =
      LinearMap.comp (σ₁₃ := g.comp f) (augmentationCotangentMapRingHom N g ψ)
        (augmentationCotangentMapRingHom M f φ) := by
    apply augmentationCotangent_semilinearMap_ext R M
    intro m
    simp
  exact DFunLike.congr_fun h x

/-- The combined arrow respects the coefficient-left action on every class. -/
theorem augmentationCotangentMapRingHom_smul
    (f : R →+* S) (φ : M →* N) (r : R) (x : AugmentationCotangent R M) :
    augmentationCotangentMapRingHom M f φ (r • x) =
      f r • augmentationCotangentMapRingHom M f φ x :=
  (augmentationCotangentMapRingHom M f φ).map_smulₛₗ r x

/-- Scalar-labelled generators under combined covariance. -/
theorem augmentationCotangentMapRingHom_smul_delta
    (f : R →+* S) (φ : M →* N) (r : R) (m : M) :
    augmentationCotangentMapRingHom M f φ (r • augmentationCotangentDelta R M m) =
      f r • augmentationCotangentDelta S N (φ m) := by simp

section TensorNaturality

variable {G : Type w} {H : Type u₁} [Group G] [Group H]

/-- The tensor arrow on group-labelled pure tensors. -/
theorem augmentationCotangentTensorMap_tmul_of
    (f : R →+* S) (φ : G →* H) (r : R) (g : G) :
    augmentationCotangentTensorMap f φ (r ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of g)) =
      f r ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of (φ g)) := by simp

/-- The same integer tensor arrow bundled for its coefficient-left semilinearity. -/
noncomputable def augmentationCotangentTensorMapSemilinear (f : R →+* S) (φ : G →* H) :
    R ⊗[ℤ] Additive (Abelianization G) →ₛₗ[f]
      S ⊗[ℤ] Additive (Abelianization H) where
  toFun := augmentationCotangentTensorMap f φ
  map_add' := (augmentationCotangentTensorMap f φ).map_add
  map_smul' := augmentationCotangentTensorMap_smul f φ

/-- The semilinear bundle has the underlying integer tensor arrow. -/
@[simp] theorem augmentationCotangentTensorMapSemilinear_apply
    (f : R →+* S) (φ : G →* H) (x : R ⊗[ℤ] Additive (Abelianization G)) :
    augmentationCotangentTensorMapSemilinear f φ x = augmentationCotangentTensorMap f φ x := rfl

/-- The identity coefficient and group arrows give the identity integer tensor map. -/
@[simp] theorem augmentationCotangentTensorMap_id :
    augmentationCotangentTensorMap (RingHom.id R) (MonoidHom.id G) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Tensor covariance composes in both variables. -/
theorem augmentationCotangentTensorMap_comp
    {T : Type*} [Ring T] {K : Type*} [Group K]
    (f : R →+* S) (g : S →+* T) (φ : G →* H) (ψ : H →* K) :
    augmentationCotangentTensorMap (g.comp f) (ψ.comp φ) =
      (augmentationCotangentTensorMap g ψ).comp (augmentationCotangentTensorMap f φ) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r a => simp [Abelianization.map_map_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Fixed-coefficient naturality of the cotangent comparison, on every class. -/
theorem augmentationCotangentTensorEquiv_natural
    (φ : G →* H) (x : AugmentationCotangent R G) :
    augmentationCotangentTensorEquiv R H (augmentationCotangentMap R G φ x) =
      augmentationCotangentTensorMap (RingHom.id R) φ
        (augmentationCotangentTensorEquiv R G x) := by
  have h : (augmentationCotangentTensorEquiv R H).toLinearMap.comp
      (augmentationCotangentMap R G φ) =
      (augmentationCotangentTensorMapSemilinear (RingHom.id R) φ).comp
        (augmentationCotangentTensorEquiv R G).toLinearMap := by
    apply augmentationCotangent_linearMap_ext R G
    intro g
    simp
  exact DFunLike.congr_fun h x

/-- The comparison commutes with simultaneous coefficient and group covariance. -/
theorem augmentationCotangentTensorEquiv_mapRingHom
    (f : R →+* S) (φ : G →* H) (x : AugmentationCotangent R G) :
    augmentationCotangentTensorEquiv S H (augmentationCotangentMapRingHom G f φ x) =
      augmentationCotangentTensorMap f φ (augmentationCotangentTensorEquiv R G x) := by
  have h : (augmentationCotangentTensorEquiv S H).toLinearMap.comp
      (augmentationCotangentMapRingHom G f φ) =
      (augmentationCotangentTensorMapSemilinear f φ).comp
        (augmentationCotangentTensorEquiv R G).toLinearMap := by
    apply augmentationCotangent_semilinearMap_ext R G
    intro g
    simp
  exact DFunLike.congr_fun h x

end TensorNaturality

/-- The delta class of a pair splits without a group hypothesis. -/
theorem augmentationCotangentDelta_prod (m : M) (n : N) :
    augmentationCotangentDelta R (M × N) (m, n) =
      augmentationCotangentDelta R (M × N) (m, 1) +
        augmentationCotangentDelta R (M × N) (1, n) := by
  simpa using augmentationCotangentDelta_mul R (M × N) (m, 1) (1, n)

/-- Product projection sends a delta class to its two coordinates. -/
@[simp] theorem augmentationCotangentProdMap_delta (m : M) (n : N) :
    augmentationCotangentProdMap (R := R) M (augmentationCotangentDelta R (M × N) (m, n)) =
      (augmentationCotangentDelta R M m, augmentationCotangentDelta R N n) := by
  simp [augmentationCotangentProdMap_apply]

/-- Projection of the first inclusion is the first coordinate inclusion. -/
@[simp] theorem augmentationCotangentProdMap_inl (x : AugmentationCotangent R M) :
    augmentationCotangentProdMap M (augmentationCotangentMap R M (MonoidHom.inl M N) x) =
      (x, 0) := by
  have h : (augmentationCotangentProdMap (R := R) M).comp
      (augmentationCotangentMap R M (MonoidHom.inl M N)) =
      (LinearMap.id : AugmentationCotangent R M →ₗ[R] _).prod
        (0 : AugmentationCotangent R M →ₗ[R] AugmentationCotangent R N) := by
    apply augmentationCotangent_linearMap_ext R M
    intro m
    simp
  exact DFunLike.congr_fun h x

/-- Projection of the second inclusion is the second coordinate inclusion. -/
@[simp] theorem augmentationCotangentProdMap_inr (y : AugmentationCotangent R N) :
    augmentationCotangentProdMap M (augmentationCotangentMap R N (MonoidHom.inr M N) y) =
      (0, y) := by
  have h : (augmentationCotangentProdMap (R := R) M).comp
      (augmentationCotangentMap R N (MonoidHom.inr M N)) =
      (0 : AugmentationCotangent R N →ₗ[R] AugmentationCotangent R M).prod
        (LinearMap.id : AugmentationCotangent R N →ₗ[R] _) := by
    apply augmentationCotangent_linearMap_ext R N
    intro n
    simp
  exact DFunLike.congr_fun h y

/-- Inclusion followed by projection is the identity on the pair of cotangents. -/
@[simp] theorem augmentationCotangentProdMap_inv
    (p : AugmentationCotangent R M × AugmentationCotangent R N) :
    augmentationCotangentProdMap M (augmentationCotangentProdInv M p) = p := by
  rcases p with ⟨x, y⟩
  simp [augmentationCotangentProdInv_apply]

/-- Projection followed by inclusion is the identity on the product cotangent. -/
@[simp] theorem augmentationCotangentProdInv_map (x : AugmentationCotangent R (M × N)) :
    augmentationCotangentProdInv M (augmentationCotangentProdMap M x) = x := by
  have h : (augmentationCotangentProdInv (R := R) (N := N) M).comp
      (augmentationCotangentProdMap M) = LinearMap.id := by
    apply augmentationCotangent_linearMap_ext R (M × N)
    rintro ⟨m, n⟩
    simpa [augmentationCotangentProdInv_apply] using
      (augmentationCotangentDelta_prod (R := R) M m n).symm
  exact DFunLike.congr_fun h x

/-- The cotangent of a binary monoid product is the product of its cotangents. -/
noncomputable def augmentationCotangentProdEquiv :
    AugmentationCotangent R (M × N) ≃ₗ[R]
      AugmentationCotangent R M × AugmentationCotangent R N where
  toLinearMap := augmentationCotangentProdMap M
  invFun := augmentationCotangentProdInv M
  left_inv := augmentationCotangentProdInv_map M
  right_inv := augmentationCotangentProdMap_inv M

/-- The forward equivalence is the pair of projections. -/
@[simp] theorem augmentationCotangentProdEquiv_apply
    (x : AugmentationCotangent R (M × N)) :
    augmentationCotangentProdEquiv (R := R) M x = augmentationCotangentProdMap M x := rfl

/-- The inverse equivalence is the sum of the two inclusions. -/
@[simp] theorem augmentationCotangentProdEquiv_symm_apply
    (p : AugmentationCotangent R M × AugmentationCotangent R N) :
    (augmentationCotangentProdEquiv (R := R) M).symm p =
      augmentationCotangentProdInv M p := rfl

/-- The product equivalence on a monoid-labelled delta class. -/
theorem augmentationCotangentProdEquiv_delta (m : M) (n : N) :
    augmentationCotangentProdEquiv (R := R) M
      (augmentationCotangentDelta R (M × N) (m, n)) =
      (augmentationCotangentDelta R M m, augmentationCotangentDelta R N n) := by simp

/-- Scalar-labelled delta classes split coordinatewise. -/
theorem augmentationCotangentProdEquiv_smul_delta (r : R) (m : M) (n : N) :
    augmentationCotangentProdEquiv (R := R) M
      (r • augmentationCotangentDelta R (M × N) (m, n)) =
      (r • augmentationCotangentDelta R M m, r • augmentationCotangentDelta R N n) := by
  rw [map_smul, augmentationCotangentProdEquiv_delta]
  rfl


/-- Coefficient covariance on every scalar multiple of an augmentation class. -/
theorem augmentationCotangentCoeffMap_smul_toAugmentationCotangent
    (f : R →+* S) (r : R) (x : RingHom.ker (augmentation R M)) :
    augmentationCotangentCoeffMap M f (r • toAugmentationCotangent R M x) =
      f r • toAugmentationCotangent S M ⟨mapRingHom M f x, by
        change augmentation S M (mapRingHom M f x) = 0
        rw [augmentation_mapRingHom, x.property, map_zero]⟩ := by
  rw [augmentationCotangentCoeffMap_smul,
    augmentationCotangentCoeffMap_toAugmentationCotangent]

/-- The full image formula in the opposite order of coefficient and monoid change. -/
theorem augmentationCotangentMapRingHom_toAugmentationCotangent_coeff_after_domain
    (f : R →+* S) (φ : M →* N) (x : RingHom.ker (augmentation R M)) :
    augmentationCotangentMapRingHom M f φ (toAugmentationCotangent R M x) =
      toAugmentationCotangent S N ⟨mapRingHom N f (mapDomainRingHom R φ x), by
        change augmentation S N (mapRingHom N f (mapDomainRingHom R φ x)) = 0
        rw [augmentation_mapRingHom]
        have h := (DFunLike.congr_fun (augmentation_comp_mapDomainRingHom R M φ)
          (x : MonoidAlgebra R M)).trans x.property
        simpa only [RingHom.comp_apply, map_zero] using congrArg f h⟩ := by
  rw [augmentationCotangentMapRingHom_eq_coeffMap_comp, LinearMap.comp_apply,
    augmentationCotangentMap_toAugmentationCotangent_image,
    augmentationCotangentCoeffMap_toAugmentationCotangent]

section TensorCoherence

variable {G : Type w} {H : Type u₁} [Group G] [Group H]

/-- The semilinear tensor bundle preserves identity arrows. -/
@[simp] theorem augmentationCotangentTensorMapSemilinear_id :
    augmentationCotangentTensorMapSemilinear (RingHom.id R) (MonoidHom.id G) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp

/-- The semilinear tensor bundle respects composition on every tensor. -/
theorem augmentationCotangentTensorMapSemilinear_comp
    {T : Type*} [Ring T] {K : Type*} [Group K]
    (f : R →+* S) (g : S →+* T) (φ : G →* H) (ψ : H →* K)
    (x : R ⊗[ℤ] Additive (Abelianization G)) :
    augmentationCotangentTensorMapSemilinear (g.comp f) (ψ.comp φ) x =
      augmentationCotangentTensorMapSemilinear g ψ
        (augmentationCotangentTensorMapSemilinear f φ x) := by
  simpa only [augmentationCotangentTensorMapSemilinear_apply, LinearMap.comp_apply] using
    DFunLike.congr_fun (augmentationCotangentTensorMap_comp f g φ ψ) x

end TensorCoherence

end MonoidAlgebra
