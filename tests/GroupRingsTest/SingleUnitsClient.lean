/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings

/-!
# Single-term units and nonunits over the natural-number semiring

The basis term at the positive generator of the integer index monoid is a
nonidentity unit. The coefficient semiring need not be a ring, and the inverse
is verified directly from the stock monoid-algebra multiplication laws.
In contrast, the basis term at `2` in the ordinary multiplicative monoid `ℕ`
is not a unit, by the single-term criterion; this index monoid is not a group.
-/

open MonoidAlgebra

noncomputable section

example :
    IsUnit (single (Multiplicative.ofAdd (1 : ℤ)) (1 : ℕ)) ∧
    (single (Multiplicative.ofAdd (1 : ℤ)) (1 : ℕ) :
      MonoidAlgebra ℕ (Multiplicative ℤ)) ≠ 1 := by
  constructor
  · refine isUnit_iff_exists.mpr
      ⟨single (Multiplicative.ofAdd (-1 : ℤ)) (1 : ℕ), ?_, ?_⟩ <;>
      simp [MonoidAlgebra.one_def]
  · intro h
    have hcoeff := congrArg
      (fun x : MonoidAlgebra ℕ (Multiplicative ℤ) =>
        x.coeff (Multiplicative.ofAdd (1 : ℤ))) h
    simp [MonoidAlgebra.one_def] at hcoeff

example : ¬ IsUnit (single (2 : ℕ) (1 : ℕ)) := by
  simp [MonoidAlgebra.isUnit_single_iff]
