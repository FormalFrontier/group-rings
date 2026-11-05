/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.Augmentation
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
  let _ : Module.Projective (MonoidAlgebra R G) R := hprojective
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property
    (Module.compHom.toLinearMap (augmentation R G))
    (LinearMap.id : R →ₗ[MonoidAlgebra R G] R) (augmentation_surjective R G)
  let x : MonoidAlgebra R G := σ 1
  have hx_augmentation : augmentation R G x = 1 :=
    LinearMap.congr_fun hσ 1
  have hx_fixed (g : G) : single g 1 * x = x := by
    have haction : (single g (1 : R) : MonoidAlgebra R G) • (1 : R) = 1 := by
      rw [RingHom.toModule_smul, augmentation_single, one_mul]
    calc
      single g 1 * x = σ ((single g (1 : R) : MonoidAlgebra R G) • (1 : R)) :=
        (σ.map_smul (single g 1) 1).symm
      _ = x := by rw [haction]
  classical
  have hx_coeff (g : G) : x.coeff g = x.coeff 1 := by
    have h := congrArg (fun y : MonoidAlgebra R G => y.coeff 1) (hx_fixed g⁻¹)
    simpa only [coeff_single_mul_apply, one_mul, inv_inv, mul_one] using h
  have hc : x.coeff 1 ≠ 0 := by
    intro hc
    have hx_zero : x.coeff = 0 := Finsupp.ext fun g => (hx_coeff g).trans hc
    apply (zero_ne_one : (0 : R) ≠ 1)
    calc
      (0 : R) = augmentation R G x := by
        rw [augmentation_apply, hx_zero, Finsupp.sum_zero_index]
      _ = 1 := hx_augmentation
  have hsupport (g : G) : g ∈ x.coeff.support := by
    rw [Finsupp.mem_support_iff, hx_coeff]
    exact hc
  have hfinite : Finite G := Finite.of_finite_univ
    (x.coeff.support.finite_toSet.subset fun g _ => hsupport g)
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
