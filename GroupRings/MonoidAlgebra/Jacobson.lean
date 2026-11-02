/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Nilpotent.Defs
public import GroupRings.MonoidAlgebra.AugmentationNilpotence.LocallyFinite

import Mathlib.RingTheory.Nilpotent.Basic
import GeneralLinearGroups.QuasiregularIdeal

/-!
# Jacobson radicals of locally finite p-group algebras

Over a ring in which the prime `p` vanishes, the augmentation kernel of a
locally finite `p`-group algebra is nil: each of its elements is nilpotent.
The exponent may depend on the element; no uniform exponent or vanishing power
of the whole augmentation ideal is asserted.

Local finiteness is expressed by the finite-closure hypothesis
`∀ s : Finset G, Finite (Subgroup.closure (s : Set G))`: every finite subset
of `G` generates a finite subgroup. No finite generating set or subgroup
exhaustion is chosen, and `G` need not be finite or abelian.

The Jacobson radical is the inverse image of the coefficient ring's Jacobson
radical under augmentation. Here `Ring.jacobson` is the two-sided Jacobson
radical, represented as an `Ideal`. Consequently, radical membership depends
on the sum of the coefficients, and a basis monomial belongs to the radical
exactly when its coefficient does. If the coefficient ring has zero Jacobson
radical, the group-algebra radical is precisely the augmentation kernel.

The coefficient ring may be noncommutative or zero. The coefficient and group
universes are independent.

## References

The elementwise nilness theorem is supplied by
`AugmentationNilpotence.LocallyFinite`; its finite-support reduction uses
`augmentation_pow_card_eq_bot`. The radical
argument uses Mathlib's surjective Jacobson-radical correspondence and the
quasiregular-ideal criterion of the `GeneralLinearGroups` library.
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

variable {R : Type u} [Ring R] {G : Type v} [Group G] {p : ℕ}

/-- The Jacobson radical of a locally finite `p`-group algebra is the augmentation
preimage of the coefficient radical, over any ring with `p = 0`.
This combines Mathlib's Jacobson-radical correspondence with the quasiregular-ideal
criterion of the `GeneralLinearGroups` library. -/
theorem jacobson_eq_comap_augmentation (hp : p.Prime) (hR : (p : R) = 0)
    (hG : IsPGroup p G)
    (hfin : ∀ s : Finset G, Finite (Subgroup.closure (s : Set G))) :
    Ring.jacobson (MonoidAlgebra R G) =
      Ideal.comap (augmentation R G) (Ring.jacobson R) := by
  have hq : (TwoSidedIdeal.ker (augmentation R G)).IsQuasiregular := by
    apply (TwoSidedIdeal.isQuasiregular_iff_forall_isUnit_one_add _).2
    intro x hx
    exact (isNilpotent_of_augmentation_eq_zero hp hR hG hfin x
      ((TwoSidedIdeal.mem_ker (augmentation R G)).mp hx)).isUnit_one_add
  have hker : RingHom.ker (augmentation R G) ≤ Ring.jacobson (MonoidAlgebra R G) := by
    intro x hx
    apply Ideal.mem_toTwoSided.mp
    exact (TwoSidedIdeal.le_iff.mp hq.le_ringJacobson)
      ((TwoSidedIdeal.mem_ker (augmentation R G)).mpr (RingHom.mem_ker.mp hx))
  rw [← Ideal.jacobson_bot (R := R),
    Ideal.comap_jacobson_of_surjective (augmentation_surjective R G),
    ← RingHom.ker_eq_comap_bot]
  apply le_antisymm Ideal.ringJacobson_le_jacobson
  calc
    (RingHom.ker (augmentation R G)).jacobson ≤
        (Ring.jacobson (MonoidAlgebra R G)).jacobson := Ideal.jacobson_mono hker
    _ = Ring.jacobson (MonoidAlgebra R G) := by
      simpa only [Ideal.jacobson_bot] using
        (Ideal.jacobson_idem (I := (⊥ : Ideal (MonoidAlgebra R G))))

/-- An element of a locally finite `p`-group algebra lies in the Jacobson radical
exactly when its augmentation lies in the coefficient radical, over a ring with `p = 0`. -/
theorem mem_jacobson_iff_augmentation_mem (hp : p.Prime) (hR : (p : R) = 0)
    (hG : IsPGroup p G)
    (hfin : ∀ s : Finset G, Finite (Subgroup.closure (s : Set G)))
    (x : MonoidAlgebra R G) :
    x ∈ Ring.jacobson (MonoidAlgebra R G) ↔ augmentation R G x ∈ Ring.jacobson R := by
  rw [jacobson_eq_comap_augmentation hp hR hG hfin]
  rfl

/-- A basis monomial in a locally finite `p`-group algebra lies in the Jacobson
radical exactly when its coefficient does, over a ring with `p = 0`.
The case `g = 1` gives the coefficient-inclusion criterion. -/
theorem single_mem_jacobson_iff (hp : p.Prime) (hR : (p : R) = 0)
    (hG : IsPGroup p G)
    (hfin : ∀ s : Finset G, Finite (Subgroup.closure (s : Set G)))
    (g : G) (r : R) :
    single g r ∈ Ring.jacobson (MonoidAlgebra R G) ↔ r ∈ Ring.jacobson R := by
  simpa only [augmentation_single] using
    mem_jacobson_iff_augmentation_mem hp hR hG hfin (single g r)

/-- If the coefficient ring has zero Jacobson radical, the radical of its locally
finite `p`-group algebra is the augmentation kernel, provided `p = 0` in the ring. -/
theorem jacobson_eq_ker_augmentation_of_jacobson_eq_bot
    (hp : p.Prime) (hR : (p : R) = 0) (hG : IsPGroup p G)
    (hfin : ∀ s : Finset G, Finite (Subgroup.closure (s : Set G)))
    (hJ : Ring.jacobson R = ⊥) :
    Ring.jacobson (MonoidAlgebra R G) = RingHom.ker (augmentation R G) := by
  rw [jacobson_eq_comap_augmentation hp hR hG hfin, hJ, RingHom.ker_eq_comap_bot]

end MonoidAlgebra
