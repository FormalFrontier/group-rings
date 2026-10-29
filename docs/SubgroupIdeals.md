# Subgroup augmentation ideals

Let `R` be a possibly noncommutative unital ring, `G` a group and `H` a
subgroup. All statements allow independent universes for `R` and `G`.
In `MonoidAlgebra R G`, write

```lean
Ideal.span (Set.range (fun h : H => MonoidAlgebra.single (h : G) (1 : R) - 1))
```

for the subgroup's **left** ideal. This is ordinary left span, not two-sided
span or normal closure. It is kept inline in the public theorem statements.

## Coset coefficients

`MonoidAlgebra.cosetSum R H` is an `R`-linear map

```lean
MonoidAlgebra R G →ₗ[R] (G ⧸ H →₀ R)
```

sending `single g r` to `Finsupp.single (QuotientGroup.mk g) r`. Its construction
needs only `Semiring R`. The target is a coefficient module indexed by **left
cosets `gH`**; no normality of `H`, quotient group, or quotient ring is needed.
`cosetSum_single` is a simp law; `cosetSum_apply` expresses each coefficient as
a sum over the finite support of the input. There is no finiteness assumption
on `G`, `H`, or `G ⧸ H`.

For any ring `R`, `MonoidAlgebra.mem_span_subgroup_iff` states that an arbitrary
element belongs to the displayed ideal if and only if its coset sum is zero.
This includes the zero ring. The reverse implication compares each group basis
term with a chosen representative of its coset; their difference is a left
multiple of a subgroup generator. Only finitely many input coefficients occur.

The coset map is not asserted to be a ring homomorphism. Group-basis left
translations are coefficient-linear, but arbitrary left multiplication need
not be: in a convolution the coefficient products have order `a_x * f_y`.
Noncommuting coefficient factors cannot be reversed.

## Reflection and two-sidedness

With `Nontrivial R`, the following are equivalent pairs:

| Theorem | Equivalence |
| --- | --- |
| `single_sub_one_mem_span_subgroup_iff` | `single g 1 - 1` belongs to the left ideal iff `g ∈ H`. |
| `span_subgroup_le_iff` | The left ideal for `H` is contained in that for `K` iff `H ≤ K`. |
| `span_subgroup_isTwoSided_iff` | The left ideal is two-sided iff `H.Normal`. |

No normality assumption is used for the first two equivalences.
The forward inclusion of ideals follows directly from `Ideal.span_mono` and
holds without `Nontrivial R`. The theorem `span_subgroup_isTwoSided` likewise
retains the all-ring implication from normality to two-sidedness.
`Ideal.subset_span` and `Ideal.span_le` provide the generator and least-span
interfaces without additional subgroup-specific wrappers.

Nontriviality is essential only for reflection: in the zero ring all the basis
differences vanish and all these ideals coincide, regardless of the subgroup.
No coefficient or group commutativity, field/domain condition, finite-group
hypothesis, decidable equality parameter, or nontrivial-group assumption is added.

The [public-import client](../tests/GroupRingsTest/SubgroupIdealsClient.lean)
uses `R = Matrix (Fin 2) (Fin 2) ℤ` and the stabilizer of `2` in `S₃`.
The difference at `(01)` belongs to its left ideal, whereas its right translate
by `(12)` has a nonzero coset coefficient and hence does not belong. The same
client exhibits the coefficient-order obstruction with matrix units. It uses
the characteristic theorem to deduce nonmembership, rather than treating a
coset calculation alone as an ideal-membership theorem.

Import `GroupRings` or `GroupRings.MonoidAlgebra.SubgroupIdeals` to use this API.
