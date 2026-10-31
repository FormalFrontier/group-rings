/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Artinian.Module

@[expose] public section

/-!
# Artinian Laurent polynomial rings

A Laurent polynomial ring over an arbitrary ring is left Artinian exactly when its
coefficient ring is subsingleton. Coefficient multiplication need not be commutative.
The scalar ring in `IsArtinianRing` is the Laurent polynomial ring itself, not its
coefficient ring.

The obstruction is the regular nonunit `T 1 - 1`. The generic Artinian regularity
criterion is the same one used for polynomial rings in
`MultivariatePolynomials.Artinian`; the polynomial variable itself cannot serve as
this obstruction because it becomes a unit in the Laurent polynomial ring.

## References

* Mathlib, `Mathlib.Algebra.Polynomial.Laurent`: Laurent polynomials and their monomials.
* Mathlib, `Mathlib.RingTheory.Artinian.Module`: right-regular elements are units in a
  left Artinian semiring.
* `MultivariatePolynomials.Artinian`: the regular-nonunit obstruction for polynomial
  semirings, including noncommutative coefficients.
-/

universe u

namespace LaurentPolynomial

variable {R : Type u}

section Semiring

variable [Semiring R]

/-- Multiplication by a Laurent monomial shifts coefficients. -/
@[simp]
theorem coeff_mul_T (f : LaurentPolynomial R) (m n : ℤ) :
    (f * T n).coeff m = f.coeff (m - n) := by
  simp only [T, AddMonoidAlgebra.coeff_mul_single_apply, mul_one, sub_eq_add_neg]

/-- Right multiplication by a constant multiplies each coefficient on the right. -/
@[simp]
theorem coeff_mul_C (f : LaurentPolynomial R) (r : R) (n : ℤ) :
    (f * C r).coeff n = f.coeff n * r := by
  rw [← single_eq_C]
  exact AddMonoidAlgebra.coeff_mul_single_zero f r n

/-- Left multiplication by a constant multiplies each coefficient on the left. -/
@[simp]
theorem coeff_C_mul (f : LaurentPolynomial R) (r : R) (n : ℤ) :
    (C r * f).coeff n = r * f.coeff n := by
  rw [← single_eq_C]
  exact AddMonoidAlgebra.coeff_single_zero_mul f r n

private noncomputable def evalOne : LaurentPolynomial R →+* R :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id R) (1 : Multiplicative ℤ →* R)
    (fun r _ ↦ Commute.one_right r)

end Semiring

section Ring

variable [Ring R]

-- A nonzero finite support has a largest exponent, whose successor coefficient vanishes.
private theorem eq_zero_of_coeff_succ (f : LaurentPolynomial R)
    (h : ∀ n : ℤ, f.coeff (n + 1) = 0 → f.coeff n = 0) : f = 0 := by
  classical
  apply LaurentPolynomial.ext
  intro n
  change f.coeff n = 0
  by_contra hn
  have hs : f.coeff.support.Nonempty := ⟨n, Finsupp.mem_support_iff.mpr hn⟩
  let m := f.coeff.support.max' hs
  have hm : m ∈ f.coeff.support := Finset.max'_mem _ _
  have hz : f.coeff (m + 1) = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have hle : m + 1 ≤ m := Finset.le_max' _ _ hmem
    omega
  exact Finsupp.mem_support_iff.mp hm (h m hz)

/-- The monic Laurent difference `T 1 - C r` is left- and right-regular, even when
coefficients do not commute or the coefficient ring is trivial. -/
theorem isRegular_T_sub_C (r : R) : IsRegular (T 1 - C r) := by
  constructor
  · apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
    intro f hf
    apply eq_zero_of_coeff_succ f
    intro n hn
    have hc := congrArg (fun g : LaurentPolynomial R ↦ g.coeff (n + 1)) hf
    simpa [sub_mul, hn] using hc
  · apply isRightRegular_iff_left_eq_zero_of_mul.mpr
    intro f hf
    apply eq_zero_of_coeff_succ f
    intro n hn
    have hc := congrArg (fun g : LaurentPolynomial R ↦ g.coeff (n + 1)) hf
    simpa [mul_sub, hn] using hc

/-- Evaluation at one shows that `T 1 - 1` is not a unit over a nontrivial ring.
No commutativity of the coefficients is needed. -/
theorem not_isUnit_T_sub_one [Nontrivial R] :
    ¬IsUnit (T 1 - (1 : LaurentPolynomial R)) := by
  intro h
  have hz : IsUnit (0 : R) := by
    simpa only [map_sub, map_one, evalOne, T,
      AddMonoidAlgebra.liftNCRingHom_single, RingHom.id_apply, MonoidHom.one_apply,
      mul_one, sub_self] using h.map (evalOne (R := R))
  exact not_isUnit_zero hz

/-- A Laurent polynomial ring is left Artinian exactly when its coefficient ring is
subsingleton. The coefficient ring need not be commutative. The proof follows the
regular-nonunit method for polynomial rings in `MultivariatePolynomials.Artinian`,
using `T 1 - 1` in place of the polynomial variable. -/
theorem isArtinianRing_iff (R : Type u) [Ring R] :
    IsArtinianRing (LaurentPolynomial R) ↔ Subsingleton R := by
  constructor
  · intro h
    let : IsArtinianRing (LaurentPolynomial R) := h
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact hR
    · let : Nontrivial R := hR
      have hreg : IsRightRegular (T 1 - (1 : LaurentPolynomial R)) := by
        simpa only [map_one] using (isRegular_T_sub_C (1 : R)).right
      exact (not_isUnit_T_sub_one
        (IsArtinianRing.isUnit_iff_isRightRegular.mpr hreg)).elim
  · intro h
    let : Subsingleton R := h
    exact isArtinian_of_finite (R := LaurentPolynomial R) (M := LaurentPolynomial R)

end Ring

end LaurentPolynomial
