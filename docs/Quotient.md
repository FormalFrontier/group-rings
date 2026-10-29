# Group rings of normal-subgroup quotients

Import `GroupRings` or `GroupRings.MonoidAlgebra.Quotient`.
Let `R` be any ring, `G` any group, and `N : Subgroup G` a normal subgroup.
The coefficient ring can be noncommutative or trivial. All universes are
independent, and neither group nor quotient is assumed finite.

The map is the existing
`MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' N)`. Its surjectivity follows
from `MonoidAlgebra.mapDomainRingHom_surjective` and
`QuotientGroup.mk'_surjective`. The theorem `coeff_mapDomainRingHom_mk'`
identifies its coefficient function on every input with `cosetSum R N`.
This bridge only requires semiring coefficients.

## The quotient equivalence

Write `J` in this guide for the independently specified left ideal

```lean
Ideal.span (Set.range fun n : N =>
  MonoidAlgebra.single (n : G) (1 : R) - 1)
```

`ker_mapDomainRingHom_mk'` identifies this span with the kernel. Normality
makes the span two-sided by `span_subgroup_isTwoSided`; the quotient module
provides this as an instance. Neither the ideal nor the index map is replaced
by a new definition.

`quotientSpanSubgroupEquiv R N` is a ring equivalence from
`MonoidAlgebra R G ⧸ J` to `MonoidAlgebra R (G ⧸ N)`. Its public formulas are:

- `quotientSpanSubgroupEquiv_mk`: the class of every `f` maps to its canonical
  index-map image;
- `quotientSpanSubgroupEquiv_mk_single`: the class of `single g r` maps to
  `single (QuotientGroup.mk' N g) r`, for every coefficient `r`;
- `quotientSpanSubgroupEquiv_unique`: values on all quotient classes determine
  the equivalence uniquely.

The all-element characteristic formula is a simp lemma; the full basis
formula also follows by `simp` using the index-map API. In particular coefficients
are copied unchanged, not augmented, centralized, or restricted to one.
There is no `AlgEquiv R` claim when `R` is noncommutative.

## Universal property

For any semiring `S` and any unital ring homomorphism
`θ : MonoidAlgebra R G →+* S`, the theorem
`existsUnique_comp_mapDomainRingHom_mk'_iff R N θ` says that there exists a
unique `ψ : MonoidAlgebra R (G ⧸ N) →+* S` whose composite with the canonical
index map is `θ` if and only if `θ (single (n : G) 1) = 1` for every `n : N`.
No coefficient-linearity hypothesis is imposed on `θ`, and `S` need not carry
a ring structure.

`span_subgroup_le_ker_iff` expresses the relation condition as annihilation
of the left span, even for a subgroup that is not normal. Its proof uses
subtraction only in the source ring. The factorization is obtained by
`Ideal.Quotient.lift` composed with the inverse quotient equivalence.
`comp_mapDomainRingHom_mk'_single` recovers the factor's value on every full
basis term directly from its composition identity. The generic client in
`tests/GroupRingsTest/QuotientClient.lean` uses this protocol without unfolding
the equivalence or the lift.

## Formalization sources

The coefficient-kernel argument reuses the subgroup-ideal and coset-sum API in
`GroupRings.MonoidAlgebra.SubgroupIdeals`. The construction transports
Mathlib's `RingHom.quotientKerEquivOfSurjective` along the kernel equality
using `Ideal.quotEquivOfEq`; factorization reuses `Ideal.Quotient.lift`.
