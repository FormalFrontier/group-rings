/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.Augmentation
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sets

/-!
# Maps from augmentation modules to regular monoid algebras

Let `R` be a semiring and `M` a right-cancellative monoid. A nonzero
`R[M]`-linear map from `R`, with the left augmentation action, into the left
regular module `R[M]` forces `M` to be finite. Consequently, all such maps
vanish when `M` is infinite. In particular this applies to infinite groups.

The coefficient semiring need not be commutative, nontrivial, or without zero
divisors. The source action is `a • r = augmentation R M a * r`; the target
action is left multiplication in the convolution algebra. Both actions are
specified in the linear-map types below.

Infinitude is substantive: for the trivial group, the inverse of the
augmentation isomorphism is a nonzero module map over a nontrivial coefficient
semiring. Right cancellation cannot simply be omitted: an absorbing right zero
in an infinite monoid gives a nonzero invariant single term over nontrivial
coefficients.
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

/-- A linear map from the coefficient semimodule with its augmentation action
into the left regular monoid algebra is determined by its value at `1`. -/
theorem linearMap_from_augmentation_apply
    {R : Type u} {M : Type v} [Semiring R] [Monoid M]
    (f : @LinearMap (MonoidAlgebra R M) (MonoidAlgebra R M) _ _
      (RingHom.id (MonoidAlgebra R M)) R (MonoidAlgebra R M) _ _
      (augmentation R M).toModule Semiring.toModule)
    (r : R) : f r = single 1 r * f 1 := by
  let _ : Module (MonoidAlgebra R M) R := (augmentation R M).toModule
  let _ : Module (MonoidAlgebra R M) (MonoidAlgebra R M) := Semiring.toModule
  have haction : (single (1 : M) r : MonoidAlgebra R M) • (1 : R) = r := by
    rw [RingHom.toModule_smul, augmentation_single, mul_one]
  calc
    f r = f ((single (1 : M) r : MonoidAlgebra R M) • (1 : R)) := by rw [haction]
    _ = single 1 r * f 1 := f.map_smul (single (1 : M) r) 1

/-- Left multiplication by `single m 1` fixes every value of a linear map from
the augmentation semimodule into the left regular monoid algebra. -/
theorem single_one_mul_linearMap_from_augmentation_apply
    {R : Type u} {M : Type v} [Semiring R] [Monoid M]
    (f : @LinearMap (MonoidAlgebra R M) (MonoidAlgebra R M) _ _
      (RingHom.id (MonoidAlgebra R M)) R (MonoidAlgebra R M) _ _
      (augmentation R M).toModule Semiring.toModule)
    (m : M) (r : R) : single m 1 * f r = f r := by
  let _ : Module (MonoidAlgebra R M) R := (augmentation R M).toModule
  let _ : Module (MonoidAlgebra R M) (MonoidAlgebra R M) := Semiring.toModule
  have haction : (single m (1 : R) : MonoidAlgebra R M) • r = r := by
    rw [RingHom.toModule_smul, augmentation_single, one_mul]
  calc
    single m 1 * f r = f ((single m (1 : R) : MonoidAlgebra R M) • r) :=
      (f.map_smul (single m 1) r).symm
    _ = f r := by rw [haction]

/-- A nonzero linear map from the coefficient semimodule with its augmentation
action into the left regular monoid algebra forces a right-cancellative monoid
to be finite. -/
theorem finite_of_linearMap_from_augmentation_ne_zero
    {R : Type u} {M : Type v} [Semiring R] [Monoid M] [IsRightCancelMul M]
    (f : @LinearMap (MonoidAlgebra R M) (MonoidAlgebra R M) _ _
      (RingHom.id (MonoidAlgebra R M)) R (MonoidAlgebra R M) _ _
      (augmentation R M).toModule Semiring.toModule)
    (hf : f ≠ 0) : Finite M := by
  classical
  let _ : Module (MonoidAlgebra R M) R := (augmentation R M).toModule
  let _ : Module (MonoidAlgebra R M) (MonoidAlgebra R M) := Semiring.toModule
  have hx : f 1 ≠ 0 := by
    intro hzero
    apply hf
    apply LinearMap.ext
    intro r
    simpa only [LinearMap.zero_apply, hzero, mul_zero] using
      linearMap_from_augmentation_apply f r
  have hcoeff : (f 1).coeff ≠ 0 := by
    intro hzero
    apply hx
    ext
    simp [hzero]
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hcoeff
  have hsupport (m : M) :
      (f 1).coeff.support = (f 1).coeff.support.image (m * ·) := by
    have hsubset : (f 1).coeff.support ⊆ (f 1).coeff.support.image (m * ·) := by
      simpa only [single_one_mul_linearMap_from_augmentation_apply f m (1 : R)] using
        support_coeff_single_mul_subset (f 1) (1 : R) m
    exact Finset.eq_of_subset_of_card_le hsubset Finset.card_image_le
  -- Image stability follows from fixedness and finite cardinality, not from a
  -- product-support equality. Right cancellation is needed only for this injection.
  let g : M → ↥((f 1).coeff.support) := fun m =>
    ⟨m * s, by
      rw [hsupport m]
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩
  apply Finite.of_injective g
  intro m n h
  exact mul_right_cancel (congrArg Subtype.val h)

/-- Every linear map from the coefficient semimodule with its augmentation
action into the left regular algebra of an infinite right-cancellative monoid
is zero. This includes arbitrary semiring coefficients and infinite groups. -/
theorem linearMap_from_augmentation_eq_zero
    {R : Type u} {M : Type v} [Semiring R] [Monoid M] [IsRightCancelMul M] [Infinite M]
    (f : @LinearMap (MonoidAlgebra R M) (MonoidAlgebra R M) _ _
      (RingHom.id (MonoidAlgebra R M)) R (MonoidAlgebra R M) _ _
      (augmentation R M).toModule Semiring.toModule) : f = 0 := by
  by_contra hf
  let _ : Finite M := finite_of_linearMap_from_augmentation_ne_zero f hf
  exact not_finite M

end MonoidAlgebra
