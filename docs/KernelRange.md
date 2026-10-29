# Kernels and range quotients

Import `GroupRings.MonoidAlgebra.KernelRange`, or the `GroupRings` root.
Let `R` be any unital ring, `G` any group, `M` any monoid, and
`φ : G →* M`. Their universes are independent. In particular, `R` need not be
commutative or nonzero, and `M` need not be a group or cancellative.

The subgroup is the existing group-theoretic kernel `φ.ker`:
`g ∈ φ.ker ↔ φ g = 1`. It is not defined using the algebra map. Write

```lean
Ideal.span (Set.range fun n : φ.ker =>
  MonoidAlgebra.single (n : G) (1 : R) - 1)
```

for its relation ideal. This is the independently generated **left** ideal;
normality gives its two-sidedness through the subgroup-quotient API.

## Kernel and canonical equivalences

`MonoidAlgebra.ker_mapDomainRingHom R φ` identifies this ideal with the kernel
of the existing unchanged-coefficient pushforward `mapDomainRingHom R φ`.
On every basis term, that pushforward sends `single g r` to `single (φ g) r`.
Neither injectivity nor surjectivity of `φ` is required for the kernel equality.

`MonoidAlgebra.quotientSpanKerEquivMrange R φ` is a ring equivalence

\[
 R[G]/\langle [n]-1 : n\in\ker\varphi\rangle
 \;\simeq_{\mathrm{Ring}}\; R[\operatorname{mrange}(\varphi)].
\]

The target uses the stock **submonoid** `MonoidHom.mrange φ`, with its stock
monoid structure. No group instance on the range or on `M` is introduced.
The construction composes `quotientSpanSubgroupEquiv` with Mathlib's
`mapDomainRingEquiv`. Its index equivalence is selected by
`QuotientGroup.lift` of `φ.mrangeRestrict`, whose value on the class of `g`
is `φ.mrangeRestrict g`.

The characteristic lemmas are:

- `quotientSpanKerEquivMrange_mk`: on every class of `f`, the result is
  `mapDomainRingHom R φ.mrangeRestrict f`;
- `quotientSpanKerEquivMrange_mk_single`: on the class of `single g r`, the
  result is `single (φ.mrangeRestrict g) r`, for every `g` and `r`;
- `quotientSpanKerEquivMrange_unique`: the all-class formula determines the
  equivalence uniquely.

If `hφ : Function.Surjective φ`, use
`quotientSpanKerEquivOfSurjective R φ hφ` instead. It composes the range result
with the stock range-to-target equivalence, giving the monoid algebra of all
of `M`. Its `_mk`, `_mk_single`, and `_unique` lemmas have the corresponding
formulas with `φ` rather than `φ.mrangeRestrict`. These are ring equivalences,
not coefficient-algebra equivalences over a possibly noncommutative ring.

## Universal property

For any semiring `S` in a fourth independent universe and any unital
`θ : MonoidAlgebra R G →+* S`,
`existsUnique_comp_mapDomainRingHom_mrangeRestrict_iff R φ θ` says that

```lean
∃! ψ : MonoidAlgebra R (MonoidHom.mrange φ) →+* S,
  ψ.comp (mapDomainRingHom R φ.mrangeRestrict) = θ
```

if and only if `θ (single (n : G) 1) = 1` for every `n : φ.ker`.
There is no coefficient-linearity or centrality condition: `θ` is already a
ring homomorphism. The target `S` need not be a ring.

With surjective `φ`, the full-target version is
`existsUnique_comp_mapDomainRingHom_of_surjective_iff R φ hφ θ`.
For either target, `comp_mapDomainRingHom_single` gives the full coefficient
formula for every factor:

```lean
ψ (single (φ g) r) = θ (single g r)
```

Use `φ.mrangeRestrict` in this formula when `ψ` is defined on the range algebra.
The proof uses the independent subgroup-span criterion and the existing ideal
quotient lift into a semiring.

## Boundaries and a client

Killing the kernel does **not** imply extension to all of a nonsurjective
target. For example, the character taking the generator of the source integer
group to `-1` cannot extend along doubling into the integer group algebra:
an extension would require an integer unit whose square is `-1`.
The group-domain hypothesis is also essential: the sum map from the additive
monoid `ℕ²` to `ℤ` has trivial identity fiber but identifies two distinct basis
indices, so over the coefficient ring `ℤ` its algebra map has a nonzero basis
difference in its kernel.

The zero coefficient ring is included in the results. It does not allow
reflection of index injectivity or surjectivity from the algebra map without
a nontriviality assumption; the existing reflection APIs retain that boundary.

The [public-import client](../tests/GroupRingsTest/KernelRangeClient.lean) uses
noncommutative two-by-two integer matrix coefficients and `Units.coeHom ℤ`.
Its target is the multiplicative monoid of integers, and its range is proper
because zero is not a unit. It recovers quotient classes by the inverse
equivalence and constructs the augmentation factor with its full coefficient
formula through the universal-property API.
