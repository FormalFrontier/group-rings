/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import GroupRings.MonoidAlgebra.Augmentation
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# The augmentation cotangent module

For a possibly noncommutative coefficient ring and an arbitrary monoid, this is
the existing augmentation kernel modulo its ordinary ideal square.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u v w

namespace MonoidAlgebra

variable (R : Type u) (M : Type v) [Ring R] [Monoid M]

/-- The augmentation ideal modulo its ordinary product square, with coefficient scalars. -/
abbrev AugmentationCotangent : Type (max u v) :=
  RingHom.ker (augmentation R M) ⧸
    (Submodule.comap (RingHom.ker (augmentation R M)).subtype
      (RingHom.ker (augmentation R M) * RingHom.ker (augmentation R M))).restrictScalars R

/-- The canonical coefficient-linear quotient map from the augmentation kernel. -/
def toAugmentationCotangent :
    RingHom.ker (augmentation R M) →ₗ[R] AugmentationCotangent R M :=
  ((Submodule.comap (RingHom.ker (augmentation R M)).subtype
      (RingHom.ker (augmentation R M) * RingHom.ker (augmentation R M))).restrictScalars R).mkQ

theorem toAugmentationCotangent_surjective :
    Function.Surjective (toAugmentationCotangent R M) :=
  Submodule.mkQ_surjective _

theorem toAugmentationCotangent_eq_zero_iff
    (x : RingHom.ker (augmentation R M)) :
    toAugmentationCotangent R M x = 0 ↔
      (x : MonoidAlgebra R M) ∈
        RingHom.ker (augmentation R M) * RingHom.ker (augmentation R M) := by
  simp only [toAugmentationCotangent, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem, Submodule.mem_comap,
    Submodule.subtype_apply]

/-- Products of augmentation-kernel elements have zero cotangent class. -/
theorem toAugmentationCotangent_mul
    (x y : RingHom.ker (augmentation R M)) :
    toAugmentationCotangent R M
      ⟨(x : MonoidAlgebra R M) * (y : MonoidAlgebra R M),
        (RingHom.ker (augmentation R M)).mul_mem_left _ y.property⟩ = 0 :=
  (toAugmentationCotangent_eq_zero_iff R M _).2 (Ideal.mul_mem_mul x.property y.property)

/-- The class of the basis difference `[m] - 1`. -/
def augmentationCotangentDelta (m : M) : AugmentationCotangent R M :=
  toAugmentationCotangent R M ⟨single m 1 - 1, by
    simp only [RingHom.mem_ker, map_sub, augmentation_single, map_one, sub_self]⟩

theorem augmentationCotangentDelta_eq (m : M) :
    augmentationCotangentDelta R M m =
      toAugmentationCotangent R M ⟨single m 1 - 1, by
        simp only [RingHom.mem_ker, map_sub, augmentation_single, map_one, sub_self]⟩ :=
  rfl

theorem smul_augmentationCotangentDelta (r : R) (m : M) :
    r • augmentationCotangentDelta R M m =
      toAugmentationCotangent R M ⟨single m r - single 1 r, by
        simp only [RingHom.mem_ker, map_sub, augmentation_single, sub_self]⟩ := by
  rw [augmentationCotangentDelta, ← map_smul]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_smul_of_tower, smul_sub, one_def, smul_single,
    smul_eq_mul, mul_one]

theorem augmentationCotangent_ext {V : Type w} [AddCommMonoid V] [Module R V]
    {f g : AugmentationCotangent R M →ₗ[R] V}
    (h : ∀ x, f (toAugmentationCotangent R M x) = g (toAugmentationCotangent R M x)) :
    f = g := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := toAugmentationCotangent_surjective R M y
  exact h x


theorem toAugmentationCotangent_smul (r : R)
    (x : RingHom.ker (augmentation R M)) :
    r • toAugmentationCotangent R M x =
      toAugmentationCotangent R M ⟨single 1 r * (x : MonoidAlgebra R M),
        (RingHom.ker (augmentation R M)).mul_mem_left _ x.property⟩ := by
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  ext m
  simp only [Submodule.coe_smul_of_tower, coeff_smul_apply,
    coeff_single_one_mul, smul_eq_mul]

/-- The ordinary-square relation agrees with the commutative ideal cotangent relation. -/
theorem toAugmentationCotangent_eq_zero_iff_toCotangent_eq_zero
    (S : Type u) (N : Type v) [CommRing S] [CommMonoid N]
    (x : RingHom.ker (augmentation S N)) :
    toAugmentationCotangent S N x = 0 ↔
      (RingHom.ker (augmentation S N)).toCotangent x = 0 := by
  rw [toAugmentationCotangent_eq_zero_iff, Ideal.toCotangent_eq_zero, pow_two]

end MonoidAlgebra
