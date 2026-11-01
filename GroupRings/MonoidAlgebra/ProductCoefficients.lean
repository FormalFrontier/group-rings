/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Coefficients of products separate group-algebra elements

For any fixed group index, its coefficient in all right products determines a
group-algebra element. The analogous family of left products also determines the
element. In particular, either family detects zero. The identity coefficient is
the special case with index `1`.

The coefficient semiring may be zero or noncommutative, and the group need not be
finite. These criteria use the canonical group algebra and its coefficient view;
they do not require a new pairing or an augmentation map.

## References

The constructions use Mathlib's canonical monoid algebra, coefficient API and
group translations.
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

variable {R : Type u} {G : Type v} [Semiring R] [Group G]

/-- Coefficients at one fixed index in every right product determine a group-algebra element. -/
theorem eq_iff_forall_mul_coeff_eq_right (g : G) (a b : R[G]) :
    a = b ↔ ∀ c : R[G], (a * c).coeff g = (b * c).coeff g := by
  classical
  constructor
  · intro h c
    rw [h]
  · intro h
    apply coeff_injective
    apply Finsupp.ext
    intro x
    simpa [mul_assoc] using h (single (x⁻¹ * g) (1 : R))

/-- Coefficients at one fixed index in every left product determine a group-algebra element. -/
theorem eq_iff_forall_mul_coeff_eq_left (g : G) (a b : R[G]) :
    a = b ↔ ∀ c : R[G], (c * a).coeff g = (c * b).coeff g := by
  classical
  constructor
  · rintro rfl c
    rfl
  · intro h
    apply coeff_injective
    apply Finsupp.ext
    intro x
    simpa [mul_assoc] using h (single (g * x⁻¹) (1 : R))

/-- Vanishing of one fixed coefficient in every right product detects the zero element. -/
theorem eq_zero_iff_forall_mul_coeff_eq_zero_right (g : G) (a : R[G]) :
    a = 0 ↔ ∀ c : R[G], (a * c).coeff g = 0 := by
  simpa using (eq_iff_forall_mul_coeff_eq_right g a 0)

/-- Vanishing of one fixed coefficient in every left product detects the zero element. -/
theorem eq_zero_iff_forall_mul_coeff_eq_zero_left (g : G) (a : R[G]) :
    a = 0 ↔ ∀ c : R[G], (c * a).coeff g = 0 := by
  simpa using (eq_iff_forall_mul_coeff_eq_left g a (0 : R[G]))

end MonoidAlgebra
