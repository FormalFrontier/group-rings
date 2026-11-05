/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Convolution support and two unique products

For a magma with two unique products and a no-zero-divisor coefficient semiring,
convolution has at least two support elements whenever the product of the input
support cardinalities exceeds one. No associativity, identity or cancellation
law is required on the indices, and the coefficients need not commute.

The proof combines Mathlib's two-unique-products field with its uniqueness
eliminator and convolution coefficient formula. The formalization approach
reuses the unique-product API developed by Damiano Testa and Mathlib's
coefficient, finitely supported function and finite-set cardinality APIs.

## References

* Mathlib, `Algebra.Group.UniqueProds.Basic` and
  `Algebra.MonoidAlgebra.NoZeroDivisors`: unique products and convolution
  coefficients at uniquely represented products.
* Andrzej Strojnowski, *A note on u.p. groups* (1980): the classical group
  ingredient underlying Mathlib's passage from unique products to two unique
  products. The magma/semiring support estimate here is not attributed to that
  group theorem or to a transcription of the article's proof.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace MonoidAlgebra

/-- Convolution over a two-unique-products magma has more than one support element
if the product of the input support cardinalities exceeds one.

This uses Mathlib's unique-product and convolution coefficient APIs; neither the
indices nor the coefficient semiring are required to be commutative. -/
theorem one_lt_card_support_coeff_mul {R : Type u} {M : Type v}
    [Semiring R] [NoZeroDivisors R] [Mul M] [TwoUniqueProds M]
    (f g : MonoidAlgebra R M)
    (hcard : 1 < f.coeff.support.card * g.coeff.support.card) :
    1 < (f * g).coeff.support.card := by
  obtain ⟨p₁, hp₁, p₂, hp₂, hne, h₁, h₂⟩ :=
    TwoUniqueProds.uniqueMul_of_one_lt_card
      (A := f.coeff.support) (B := g.coeff.support) hcard
  obtain ⟨ha₁, hb₁⟩ := Finset.mem_product.mp hp₁
  obtain ⟨ha₂, hb₂⟩ := Finset.mem_product.mp hp₂
  have hmul : p₁.1 * p₁.2 ≠ p₂.1 * p₂.2 := by
    intro heq
    exact hne (h₁.set_subsingleton ⟨ha₁, hb₁, rfl⟩ ⟨ha₂, hb₂, heq.symm⟩)
  refine Finset.one_lt_card.mpr ⟨p₁.1 * p₁.2, ?_, p₂.1 * p₂.2, ?_, hmul⟩
  · apply Finsupp.mem_support_iff.mpr
    rw [coeff_mul_mul_of_uniqueMul h₁]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp ha₁) (Finsupp.mem_support_iff.mp hb₁)
  · apply Finsupp.mem_support_iff.mpr
    rw [coeff_mul_mul_of_uniqueMul h₂]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp ha₂) (Finsupp.mem_support_iff.mp hb₂)

end MonoidAlgebra
