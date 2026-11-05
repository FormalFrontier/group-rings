/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.AugmentationHom
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Data.Nat.Cast.Commute
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Projectivity of augmentation modules

For a group `G` over a nontrivial semiring `R`, projectivity of the coefficient
semimodule with left action `a • r = augmentation R G a * r` forces `G` to be
finite and its order to be a unit in `R`. The coefficient semiring need not be
commutative.

The augmentation is from `GroupRings.MonoidAlgebra.Augmentation`; scalar
restriction and projectivity use Mathlib's `RingHom.toModule` and
`Module.Projective`.
-/

@[expose] public section

universe uR uG

namespace MonoidAlgebra

/-- If the coefficient semimodule with its left augmentation action is projective
over the group algebra, then the group is finite and its order is a unit. -/
theorem finite_and_isUnit_natCard_of_projective_augmentation
    (R : Type uR) [Semiring R] [Nontrivial R] (G : Type uG) [Group G]
    (hprojective : @Module.Projective (MonoidAlgebra R G) inferInstance R inferInstance
      ((MonoidAlgebra.augmentation R G).toModule)) :
    Finite G ∧ IsUnit (Nat.card G : R) := by
  let _ : Module (MonoidAlgebra R G) R := (augmentation R G).toModule
  let _ : Module (MonoidAlgebra R G) (MonoidAlgebra R G) := Semiring.toModule
  let _ : Module.Projective (MonoidAlgebra R G) R := hprojective
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property
    (Module.compHom.toLinearMap (augmentation R G))
    (LinearMap.id : R →ₗ[MonoidAlgebra R G] R) (augmentation_surjective R G)
  let x : MonoidAlgebra R G := σ 1
  have hx_augmentation : augmentation R G x = 1 :=
    LinearMap.congr_fun hσ 1
  have hσ_ne_zero : σ ≠ 0 := by
    intro hzero
    apply (zero_ne_one : (0 : R) ≠ 1)
    simpa only [x, hzero, LinearMap.zero_apply, map_zero] using hx_augmentation
  have hfinite : Finite G := finite_of_linearMap_from_augmentation_ne_zero σ hσ_ne_zero
  have hx_fixed (g : G) : single g 1 * x = x :=
    single_one_mul_linearMap_from_augmentation_apply σ g 1
  classical
  have hx_coeff (g : G) : x.coeff g = x.coeff 1 := by
    have h := congrArg (fun y : MonoidAlgebra R G => y.coeff 1) (hx_fixed g⁻¹)
    simpa only [coeff_single_mul_apply, one_mul, inv_inv, mul_one] using h
  let _ : Finite G := hfinite
  let _ := Fintype.ofFinite G
  have hcard : (Nat.card G : R) * x.coeff 1 = 1 := by
    rw [augmentation_apply, Finsupp.sum_fintype _ _ (fun _ => rfl)] at hx_augmentation
    simpa only [hx_coeff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card] using hx_augmentation
  -- A one-sided inverse suffices here because natural-number casts are central.
  have hunit : IsUnit ((Nat.card G : R) * x.coeff 1) := hcard.symm ▸ isUnit_one
  exact ⟨hfinite, ((Nat.cast_commute (Nat.card G) (x.coeff 1)).isUnit_mul_iff.mp hunit).1⟩

end MonoidAlgebra
