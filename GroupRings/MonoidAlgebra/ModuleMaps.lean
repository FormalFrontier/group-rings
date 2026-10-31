/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# Linear maps between monoid-algebra modules

An additive map between modules over a monoid algebra is linear precisely when
it commutes with coefficient scalars and the canonical monoid symbols. This
criterion uses the given module structures and applies over any semiring.
-/

@[expose] public section

universe u v w r

namespace MonoidAlgebra

variable {R : Type r} {M : Type u} {V : Type v} {W : Type w}
variable [Semiring R] [Monoid M] [AddCommMonoid V] [AddCommMonoid W]
variable [Module (MonoidAlgebra R M) V] [Module (MonoidAlgebra R M) W]

/-- Coefficients and basis elements commute, even over noncommutative scalars. -/
theorem coefficient_basis_commute (r : R) (m : M) :
    (single 1 r : MonoidAlgebra R M) * single m 1 =
      single m 1 * single 1 r := by
  simp [single_mul_single]

/-- Additive maps respect every scalar precisely when they respect
coefficient scalars and canonical monoid symbols. -/
theorem map_smul_iff_coefficient_basis (f : V →+ W) :
    (∀ (x : MonoidAlgebra R M) v, f (x • v) = x • f v) ↔
    ((∀ (r : R) v, f ((single 1 r : MonoidAlgebra R M) • v) =
        (single 1 r : MonoidAlgebra R M) • f v) ∧
      (∀ (m : M) v, f ((single m 1 : MonoidAlgebra R M) • v) =
        (single m 1 : MonoidAlgebra R M) • f v)) := by
  constructor
  · intro h
    exact ⟨fun r v => h _ v, fun m v => h _ v⟩
  rintro ⟨hc, hb⟩ x v
  refine MonoidAlgebra.induction_on (motive := fun x : MonoidAlgebra R M =>
    f (x • v) = x • f v) x ?_ ?_ ?_
  · intro m
    exact hb m v
  · intro x y hx hy
    simp only [add_smul, map_add, hx, hy]
  · intro r x hx
    have h1 : r • (1 : MonoidAlgebra R M) = single 1 r := by
      change r • (single 1 (1 : R) : MonoidAlgebra R M) = _
      simp
    have he : r • x = (single 1 r : MonoidAlgebra R M) * x := by
      calc
        r • x = (r • (1 : MonoidAlgebra R M)) * x := by rw [smul_mul_assoc, one_mul]
        _ = (single 1 r : MonoidAlgebra R M) * x := by rw [h1]
    rw [he]
    simp only [mul_smul, hc, hx]

end MonoidAlgebra
