# Augmentation nilpotence and uniform group exponents

Import `GroupRings`, or
`GroupRings.MonoidAlgebra.AugmentationNilpotence.Finite` for the full criterion.
The leaf `GroupRings.MonoidAlgebra.AugmentationNilpotence` suffices for the
arbitrary-group converse.

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

## Finite p-groups: exact cardinality bound

Suppose `R` is any ring, `G` a finite group, `p` prime, `(p : R) = 0`, and
`IsPGroup p G`. Then

```lean
MonoidAlgebra.augmentation_pow_card_eq_bot hp hR hG
```

proves `I ^ Nat.card G = ⊥`. There is no coefficient commutativity,
nontriviality, field, finiteness-of-coefficients or Noetherianity assumption.
The zero ring is included using the weak equation `(p : R) = 0`, not a global
exact-characteristic typeclass.

`MonoidAlgebra.augmentation_list_prod_eq_zero` gives the equivalent statement
for every list of exactly `Nat.card G` augmentation elements, retaining their
order and allowing different or repeated factors. For **nontrivial** `R`,

```lean
MonoidAlgebra.isNilpotent_augmentation_iff_isPGroup hp hR
```

identifies canonical ideal nilpotence with `IsPGroup p G` when `G` is finite.

The proof inducts on the finite group order. Mathlib's nontrivial-center and
Cauchy theorems give a central element `z` of order `p`. The canonical quotient
map by `Subgroup.zpowers z` has kernel `Ideal.span {single z 1 - 1}` by
`MonoidAlgebra.ker_mapDomainRingHom_mk'_zpowers`. Normality makes this a
two-sided ideal. The commuting binomial identity gives `(single z 1 - 1)^p=0`,
so the kernel has zero `p`-th power, as recorded by
`MonoidAlgebra.ker_mapDomainRingHom_mk'_zpowers_pow_eq_bot`.

For the smaller quotient `G/N`, ideal extension and induction put
`I ^ Nat.card (G ⧸ N)` inside that kernel. The generic semiring inequality
`Ideal.map_pow_le` suffices: equality of extension with powers is not asserted
for arbitrary noncommutative targets. `Ideal.pow_mul` multiplies degrees for
arbitrary left ideals, including zero degrees; two-sidedness is unnecessary
for this iteration law. Lagrange's theorem gives
`Nat.card G = Nat.card (G ⧸ N) * p`, hence the required exact bound.

The [public-import client](../tests/GroupRingsTest/AugmentationNilpotenceClient.lean)
checks all mixed products of length eight for the nonabelian dihedral group of
order eight over two-by-two matrices over `ZMod 2`. It also uses the same exact
bound over `ZMod 1`, a zero ring whose characteristic is not two.

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

The finite-group iff does not extend to arbitrary infinite groups: the
uniform exponent conclusion is necessary, not sufficient. The bound is the
group cardinality, not an assertion that this is always the least nilpotence
degree.
