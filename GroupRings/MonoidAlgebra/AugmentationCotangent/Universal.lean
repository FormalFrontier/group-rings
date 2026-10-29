/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.AugmentationCotangent
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# The universal property of the augmentation cotangent module

Coefficient-linear maps out of the augmentation ideal modulo its square are
naturally identified with monoid homomorphisms to additive groups.
-/

@[expose] public section
noncomputable section
universe u v w
namespace MonoidAlgebra
variable (R : Type u) (M : Type v) [Ring R] [Monoid M]

private def augmentationDifference (m : M) : RingHom.ker (augmentation R M) :=
  ⟨single m 1 - 1, by simp⟩

private def augmentationDifferenceProduct (m n : M) :
    RingHom.ker (augmentation R M) :=
  ⟨(single m 1 - 1) * (single n 1 - 1),
    (RingHom.ker (augmentation R M)).mul_mem_left _
      (augmentationDifference R M n).property⟩

private theorem augmentationDifference_mul (m n : M) :
    augmentationDifference R M (m * n) =
      augmentationDifference R M m + augmentationDifference R M n +
        augmentationDifferenceProduct R M m n := by
  apply Subtype.ext
  change single (m * n) 1 - 1 =
    (single m 1 - 1) + (single n 1 - 1) +
      (single m 1 - 1) * (single n 1 - 1)
  have hm := single_mul_single m n (1 : R) 1
  simp only [mul_one] at hm
  rw [← hm]
  noncomm_ring

/-- The basis-difference classes turn multiplication into addition. -/
def augmentationCotangentDeltaHom :
    M →* Multiplicative (AugmentationCotangent R M) where
  toFun m := Multiplicative.ofAdd (augmentationCotangentDelta R M m)
  map_one' := by
    change toAugmentationCotangent R M (augmentationDifference R M 1) = 0
    have h : augmentationDifference R M 1 = 0 := by
      apply Subtype.ext
      simp [augmentationDifference, one_def]
    rw [h, map_zero]
  map_mul' m n := by
    change toAugmentationCotangent R M (augmentationDifference R M (m * n)) =
      toAugmentationCotangent R M (augmentationDifference R M m) +
        toAugmentationCotangent R M (augmentationDifference R M n)
    rw [augmentationDifference_mul, map_add, map_add]
    have h := toAugmentationCotangent_mul R M
      (augmentationDifference R M m) (augmentationDifference R M n)
    change toAugmentationCotangent R M (augmentationDifferenceProduct R M m n) = 0 at h
    rw [h, add_zero]

variable {V : Type w} [AddCommGroup V] [Module R V]

/-- Coefficient-linear extension of an additive monoid character to the monoid algebra. -/
def augmentationCharacterLinearMap (h : M →* Multiplicative V) :
    MonoidAlgebra R M →ₗ[R] V :=
  (Finsupp.linearCombination R (fun m => (h m).toAdd)).comp
    (coeffLinearEquiv R).toLinearMap

@[simp]
theorem augmentationCharacterLinearMap_single (h : M →* Multiplicative V)
    (m : M) (r : R) :
    augmentationCharacterLinearMap R M h (single m r) = r • (h m).toAdd := by
  exact Finsupp.linearCombination_single _ _ _

private theorem augmentationCharacterLinearMap_single_mul (h : M →* Multiplicative V)
    (m : M) (a : R) (y : MonoidAlgebra R M) :
    augmentationCharacterLinearMap R M h (single m a * y) =
      a • augmentationCharacterLinearMap R M h y +
        (a * augmentation R M y) • (h m).toAdd := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add y z hy hz =>
    simp only [mul_add, map_add, hy, hz, smul_add, add_smul]
    abel
  | single n b =>
    simp only [single_mul_single, augmentationCharacterLinearMap_single,
      augmentation_single, map_mul, toAdd_mul, mul_smul, smul_add]
    abel

private theorem augmentationCharacterLinearMap_mul (h : M →* Multiplicative V)
    (x y : MonoidAlgebra R M) (hy : augmentation R M y = 0) :
    augmentationCharacterLinearMap R M h (x * y) =
      augmentation R M x • augmentationCharacterLinearMap R M h y := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x z hx hz => simp only [add_mul, map_add, hx, hz, add_smul]
  | single m a =>
    rw [augmentationCharacterLinearMap_single_mul, hy, mul_zero, zero_smul,
      add_zero, augmentation_single]

private theorem augmentationCharacterLinearMap_square (h : M →* Multiplicative V)
    {x : MonoidAlgebra R M}
    (hx : x ∈ RingHom.ker (augmentation R M) * RingHom.ker (augmentation R M)) :
    augmentationCharacterLinearMap R M h x = 0 := by
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    rw [augmentationCharacterLinearMap_mul R M h a b hb, ha, zero_smul]
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]


private def augmentationKernelProjection :
    MonoidAlgebra R M →ₗ[R] RingHom.ker (augmentation R M) :=
  (Finsupp.linearCombination R (augmentationDifference R M)).comp
    (coeffLinearEquiv R).toLinearMap

private theorem augmentationKernelProjection_single (m : M) (r : R) :
    augmentationKernelProjection R M (single m r) =
      r • augmentationDifference R M m := by
  change Finsupp.linearCombination R _ (Finsupp.single m r) = _
  rw [Finsupp.linearCombination_single]

private theorem coe_augmentationKernelProjection (x : MonoidAlgebra R M) :
    (augmentationKernelProjection R M x : MonoidAlgebra R M) =
      x - single 1 (augmentation R M x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    change ((augmentationKernelProjection R M) (x + y) : MonoidAlgebra R M) = _
    simp only [map_add, Submodule.coe_add, hx, hy, single_add]
    abel
  | single m r =>
    rw [augmentationKernelProjection_single, augmentation_single]
    change r • (single m 1 - 1) = single m r - single 1 r
    simp only [smul_sub, one_def, smul_single, smul_eq_mul, mul_one]

private theorem augmentationKernelProjection_ker
    (x : RingHom.ker (augmentation R M)) :
    augmentationKernelProjection R M (x : MonoidAlgebra R M) = x := by
  apply Subtype.ext
  rw [coe_augmentationKernelProjection, x.property, single_zero, sub_zero]

/-- Coefficient-linear maps are determined by the basis-difference classes. -/
@[ext]
theorem augmentationCotangent_linearMap_ext {W : Type w}
    [AddCommMonoid W] [Module R W]
    {f g : AugmentationCotangent R M →ₗ[R] W}
    (h : ∀ m, f (augmentationCotangentDelta R M m) =
      g (augmentationCotangentDelta R M m)) : f = g := by
  apply augmentationCotangent_ext R M
  intro x
  have key (a : MonoidAlgebra R M) :
      f (toAugmentationCotangent R M (augmentationKernelProjection R M a)) =
        g (toAugmentationCotangent R M (augmentationKernelProjection R M a)) := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single m r =>
      simp only [augmentationKernelProjection_single, map_smul]
      exact congrArg (fun v => r • v) (h m)
  simpa only [augmentationKernelProjection_ker] using key (x : MonoidAlgebra R M)

/-- Extend an additive monoid character across the augmentation cotangent module. -/
def augmentationCotangentLift (h : M →* Multiplicative V) :
    AugmentationCotangent R M →ₗ[R] V :=
  Submodule.liftQ _
    ((augmentationCharacterLinearMap R M h).comp
      ((RingHom.ker (augmentation R M)).subtype.restrictScalars R))
    (by
      intro x hx
      exact augmentationCharacterLinearMap_square R M h hx)

@[simp]
theorem augmentationCotangentLift_toAugmentationCotangent (h : M →* Multiplicative V)
    (x : RingHom.ker (augmentation R M)) :
    augmentationCotangentLift R M h (toAugmentationCotangent R M x) =
      (x : MonoidAlgebra R M).coeff.sum (fun m r => r • (h m).toAdd) := by
  exact Finsupp.linearCombination_apply R _

@[simp]
theorem augmentationCotangentLift_delta (h : M →* Multiplicative V) (m : M) :
    augmentationCotangentLift R M h (augmentationCotangentDelta R M m) =
      (h m).toAdd := by
  change augmentationCharacterLinearMap R M h (single m 1 - 1) = _
  rw [map_sub]
  simp [one_def, augmentationCharacterLinearMap_single]

@[simp]
theorem augmentationCotangentDelta_one : augmentationCotangentDelta R M 1 = 0 :=
  congrArg Multiplicative.toAdd (augmentationCotangentDeltaHom R M).map_one

@[simp]
theorem augmentationCotangentDelta_mul (m n : M) :
    augmentationCotangentDelta R M (m * n) =
      augmentationCotangentDelta R M m + augmentationCotangentDelta R M n :=
  congrArg Multiplicative.toAdd ((augmentationCotangentDeltaHom R M).map_mul m n)

/-- Restrict a cotangent linear map to the basis-difference classes. -/
def augmentationCotangentCharacter (f : AugmentationCotangent R M →ₗ[R] V) :
    M →* Multiplicative V where
  toFun m := Multiplicative.ofAdd (f (augmentationCotangentDelta R M m))
  map_one' := by
    change f (augmentationCotangentDelta R M 1) = 0
    rw [augmentationCotangentDelta_one, map_zero]
  map_mul' m n := by
    change f (augmentationCotangentDelta R M (m * n)) =
      f (augmentationCotangentDelta R M m) + f (augmentationCotangentDelta R M n)
    rw [augmentationCotangentDelta_mul, map_add]

@[simp]
theorem augmentationCotangentCharacter_apply (f : AugmentationCotangent R M →ₗ[R] V)
    (m : M) : (augmentationCotangentCharacter R M f m).toAdd =
      f (augmentationCotangentDelta R M m) := rfl

/-- The set-valued universal property, without a module structure on linear maps. -/
def augmentationCotangentEquiv :
    (AugmentationCotangent R M →ₗ[R] V) ≃ (M →* Multiplicative V) where
  toFun := augmentationCotangentCharacter R M
  invFun := augmentationCotangentLift R M
  left_inv f := by
    apply augmentationCotangent_linearMap_ext R M
    intro m
    rw [augmentationCotangentLift_delta, augmentationCotangentCharacter_apply]
  right_inv h := by
    apply MonoidHom.ext
    intro m
    change Multiplicative.ofAdd
      (augmentationCotangentLift R M h (augmentationCotangentDelta R M m)) = h m
    simp only [augmentationCotangentLift_delta, ofAdd_toAdd]

@[simp]
theorem augmentationCotangentEquiv_apply (f : AugmentationCotangent R M →ₗ[R] V)
    (m : M) : (augmentationCotangentEquiv R M f m).toAdd =
      f (augmentationCotangentDelta R M m) := rfl

@[simp]
theorem augmentationCotangentEquiv_symm_delta (h : M →* Multiplicative V) (m : M) :
    (augmentationCotangentEquiv R M).symm h (augmentationCotangentDelta R M m) =
      (h m).toAdd :=
  augmentationCotangentLift_delta R M h m

theorem augmentationCotangentEquiv_symm_smul_delta (h : M →* Multiplicative V)
    (r : R) (m : M) :
    (augmentationCotangentEquiv R M).symm h (r • augmentationCotangentDelta R M m) =
      r • (h m).toAdd := by
  rw [map_smul, augmentationCotangentEquiv_symm_delta]


variable {W : Type*} [AddCommGroup W] [Module R W]

/-- Naturality of the universal equivalence in the target left module. -/
theorem augmentationCotangentEquiv_natural (k : V →ₗ[R] W)
    (f : AugmentationCotangent R M →ₗ[R] V) :
    augmentationCotangentEquiv R M (k.comp f) =
      (AddMonoidHom.toMultiplicative k.toAddMonoidHom).comp
        (augmentationCotangentEquiv R M f) := by
  apply MonoidHom.ext
  intro m
  rfl

/-- Naturality of character extension in the target left module. -/
theorem augmentationCotangentLift_natural (k : V →ₗ[R] W)
    (h : M →* Multiplicative V) :
    k.comp (augmentationCotangentLift R M h) =
      augmentationCotangentLift R M
        ((AddMonoidHom.toMultiplicative k.toAddMonoidHom).comp h) := by
  apply augmentationCotangent_linearMap_ext R M
  intro m
  rw [LinearMap.comp_apply, augmentationCotangentLift_delta,
    augmentationCotangentLift_delta]
  rfl

variable {N : Type*} [Monoid N]

/-- A monoid homomorphism induces a coefficient-linear map of cotangent modules. -/
def augmentationCotangentMap (φ : M →* N) :
    AugmentationCotangent R M →ₗ[R] AugmentationCotangent R N :=
  augmentationCotangentLift R M ((augmentationCotangentDeltaHom R N).comp φ)

@[simp]
theorem augmentationCotangentMap_delta (φ : M →* N) (m : M) :
    augmentationCotangentMap R M φ (augmentationCotangentDelta R M m) =
      augmentationCotangentDelta R N (φ m) :=
  augmentationCotangentLift_delta R M _ m

@[simp]
theorem augmentationCotangentMap_id :
    augmentationCotangentMap R M (MonoidHom.id M) = LinearMap.id := by
  apply augmentationCotangent_linearMap_ext R M
  intro m
  simp

theorem augmentationCotangentMap_comp {P : Type*} [Monoid P]
    (φ : M →* N) (ψ : N →* P) :
    augmentationCotangentMap R M (ψ.comp φ) =
      (augmentationCotangentMap R N ψ).comp (augmentationCotangentMap R M φ) := by
  apply augmentationCotangent_linearMap_ext R M
  intro m
  simp

/-- Naturality in the monoid, by precomposition. -/
theorem augmentationCotangentEquiv_precomp (φ : M →* N)
    (f : AugmentationCotangent R N →ₗ[R] V) :
    augmentationCotangentEquiv R M (f.comp (augmentationCotangentMap R M φ)) =
      (augmentationCotangentEquiv R N f).comp φ := by
  apply MonoidHom.ext
  intro m
  change Multiplicative.ofAdd (f (augmentationCotangentMap R M φ
    (augmentationCotangentDelta R M m))) =
      Multiplicative.ofAdd (f (augmentationCotangentDelta R N (φ m)))
  rw [augmentationCotangentMap_delta]


theorem augmentationCharacterLinearMap_apply (h : M →* Multiplicative V)
    (x : MonoidAlgebra R M) :
    augmentationCharacterLinearMap R M h x =
      x.coeff.sum (fun m r => r • (h m).toAdd) :=
  Finsupp.linearCombination_apply R _


@[simp]
theorem augmentationCotangentDeltaHom_apply (m : M) :
    (augmentationCotangentDeltaHom R M m).toAdd = augmentationCotangentDelta R M m :=
  rfl

theorem augmentationCotangentEquiv_symm_apply (h : M →* Multiplicative V) :
    (augmentationCotangentEquiv R M).symm h = augmentationCotangentLift R M h :=
  rfl

theorem augmentationCotangentMap_toAugmentationCotangent (φ : M →* N)
    (x : RingHom.ker (augmentation R M)) :
    augmentationCotangentMap R M φ (toAugmentationCotangent R M x) =
      (x : MonoidAlgebra R M).coeff.sum
        (fun m r => r • augmentationCotangentDelta R N (φ m)) := by
  simpa only [augmentationCotangentMap, MonoidHom.comp_apply,
    augmentationCotangentDeltaHom_apply] using
    augmentationCotangentLift_toAugmentationCotangent R M
      ((augmentationCotangentDeltaHom R N).comp φ) x

end MonoidAlgebra
