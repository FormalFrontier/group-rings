/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.MonoidAlgebra.Defs

import GroupRings.MonoidAlgebra.Augmentation

/-!
# Units represented by a single monoid basis term

A single term in a monoid algebra over a nontrivial semiring is a unit exactly
when its coefficient and its monoid index are units. The coefficient semiring
and index monoid need not be commutative. Coefficient-unit reflection holds
even for the zero semiring; nontriviality is needed to reflect index units.
This does not classify units represented by arbitrary finite sums.

Coefficient reflection follows by applying the augmentation homomorphism.
For a unit basis term, each inverse equation forces a monoid index whose
product with the given index is the identity: otherwise the coefficient at
the identity would vanish. The resulting left and right inverses establish
index-unit reflection without a cancellation hypothesis. The general
single-term criterion then uses the commuting coefficient and basis factors.
-/

@[expose] public section

noncomputable section

universe u v

namespace MonoidAlgebra

variable {R : Type u} {M : Type v} [Semiring R] [Monoid M]

/-- If a single monoid-algebra term is a unit, its coefficient is a unit. -/
theorem isUnit_coeff_of_single {m : M} {r : R} (h : IsUnit (single m r)) :
    IsUnit r := by
  simpa only [augmentation_single] using h.map (augmentation R M)

/-- The monoid basis embedding reflects units over a nontrivial coefficient semiring. -/
instance isLocalHom_of [Nontrivial R] : IsLocalHom (of R M) where
  map_nonunit m hm := by
    obtain ⟨x, hx, hx'⟩ := isUnit_iff_exists.mp hm
    simp only [of_apply] at hx hx'
    apply isUnit_iff_exists_and_exists.mpr
    constructor
    · by_contra! h
      have hz := coeff_single_mul_of_forall_mul_ne (1 : R) x h
      rw [hx, coeff_one_one] at hz
      exact one_ne_zero hz
    · by_contra! h
      have hz := coeff_mul_single_of_forall_mul_ne (1 : R) x h
      rw [hx', coeff_one_one] at hz
      exact one_ne_zero hz

/-- A single term is a unit exactly when both its coefficient and index are units. -/
@[simp]
theorem isUnit_single_iff [Nontrivial R] (m : M) (r : R) :
    IsUnit (single m r) ↔ IsUnit r ∧ IsUnit m := by
  constructor
  · intro h
    refine ⟨isUnit_coeff_of_single h, ?_⟩
    have hc : Commute (single (1 : M) r) (single m (1 : R)) :=
      single_commute_single (.one_left m) (.one_right r)
    have hprod : IsUnit (single (1 : M) r * single m (1 : R)) := by simpa using h
    exact IsUnit.of_map (of R M) m (hc.isUnit_mul_iff.mp hprod).2
  · intro h
    have hpair : IsUnit (r, m) := Prod.isUnit_iff.mpr h
    simpa only [singleHom_apply] using hpair.map (singleHom (R := R) (M := M))

end MonoidAlgebra
