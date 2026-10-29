# Augmentation nilpotence and uniform group exponents

Import `GroupRings`, or the leaf
`GroupRings.MonoidAlgebra.AugmentationNilpotence`.

Let `I = RingHom.ker (MonoidAlgebra.augmentation R G)`. Augmentation is the
sum of coefficients, and `I` is the existing ordinary left ideal, not a new
nilpotence model.

## Ordered products and left ideal powers

For every semiring `A`, every ordinary left ideal `I : Ideal A`, and every
natural number `n`,

```lean
Ideal.pow_eq_bot_iff_forall_list_prod_eq_zero I n
```

identifies `I ^ n = ⊥` with

```lean
∀ l : List A, l.length = n → (∀ x ∈ l, x ∈ I) → l.prod = 0
```

Factors may differ or repeat, and their order is retained. No commutativity,
two-sidedness, nontriviality or additive inverses are needed. More generally,
`Ideal.pow_le_iff_forall_list_prod_mem` characterizes containment of `I ^ n`
in another left ideal by membership of every such product.
`Ideal.list_prod_mem_pow` supplies product membership directly.

In degree zero the power is top, while the only list is empty and its product
is one. Both sides of the zero-power equivalence therefore mean `1 = 0`.
For positive degrees the proof uses Mathlib's description of additive-submonoid
powers as additive closures of ordered set products.

This is **uniform mixed nilpotence**, not merely the statement that each
individual element has some vanishing power.

## Arbitrary groups

Suppose `R` is a nontrivial ring, `G` any group, `p` prime, and `(p : R) = 0`.
The coefficient ring and group have independent universes. Neither need be
commutative; in particular `R` may be a matrix ring in prime characteristic.

* `MonoidAlgebra.forall_pow_eq_one_of_augmentation_pow_eq_bot` takes
  `I ^ n = ⊥` and `n ≤ p ^ k`, and proves `∀ g : G, g ^ (p ^ k) = 1`.
* `MonoidAlgebra.exists_pow_eq_one_of_isNilpotent_augmentation` takes the
  canonical `IsNilpotent I` and produces `∃ k, ∀ g : G, g ^ (p ^ k) = 1`.
* `MonoidAlgebra.exists_pow_eq_one_of_augmentation_products_eq_zero` takes
  uniform mixed-list-product vanishing and produces the same common exponent.
* `MonoidAlgebra.isPGroup_of_isNilpotent_augmentation` gives `IsPGroup p G`
  as a corollary.

The single exponent is chosen **before** the group element. This is stronger
than Mathlib's pointwise `IsPGroup p G`, which means `∀ g, ∃ k, ...` for an
arbitrary group. No finite-group uniform-exponent equivalence is used.

The proof first derives prime characteristic for the group ring from the weak
coefficient equation. Ideal nilpotence kills `(single g 1 - 1) ^ (p ^ k)` for
every `g` at the same degree. Mathlib's prime-characteristic binomial identity
only requires that `single g 1` commute with one. The resulting equation is
`single (g ^ (p ^ k)) 1 = 1`; the basis embedding is injective because the
coefficient ring is nontrivial.

The [public-import client](../tests/GroupRingsTest/AugmentationNilpotenceClient.lean)
checks the degree-zero boundary over arbitrary semirings and uses the uniform
conclusion to rule out augmentation nilpotence for the infinite cyclic group
over two-by-two matrices over `ZMod 2`.

## Limits

Nontriviality is essential to this implication: over the zero ring every
positive ideal power vanishes, regardless of the group. Bounded group exponent
alone does not imply augmentation nilpotence for infinite groups. For example,
in an infinite elementary abelian `p`-group, products of differences supported
on distinct coordinates remain nonzero over the prime field at arbitrary lengths.

The finite-`p`-group forward theorem with exact `Nat.card G` degree, including
the zero coefficient ring, and the finite-group equivalence remain unimplemented
here. The uniform converse does not assert either of them.
