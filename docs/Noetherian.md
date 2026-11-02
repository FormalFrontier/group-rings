# Left-Noetherian monoid and group algebras

Import `GroupRings.MonoidAlgebra.Noetherian` or the aggregate `GroupRings`.
Here `IsNoetherianRing A` concerns the regular **left** module of `A` over
itself, not the algebra as a module over its coefficients. All the criteria
below allow independent coefficient and index universes.

## Commutative monoids and groups

For `[Ring R] [CommMonoid M] [Monoid.FG M]`,
`MonoidAlgebra.isNoetherianRing_iff_of_fg` gives

```text
IsNoetherianRing (MonoidAlgebra R M) ↔ IsNoetherianRing R.
```

This packages the commutative-monoid ascent with surjective augmentation;
it is not a new ascent proof. In particular, it applies to any finitely
generated commutative group using Mathlib's group-to-monoid FG instance,
without a chosen set of coordinates or a decomposition into cyclic factors.

For `[Ring R] [CommGroup G]`, without assuming FG,
`MonoidAlgebra.isNoetherianRing_iff_of_commGroup` gives

```text
IsNoetherianRing (MonoidAlgebra R G) ↔
  IsNoetherianRing R ∧ (Subsingleton R ∨ Group.FG G).
```

Over a nonzero ring, necessity follows by applying subgroup FG necessity to
the top subgroup. Over the zero ring the group algebra is zero and hence
Noetherian, irrespective of group FG. Thus neither dropping the zero-ring
alternative nor assuming nontrivial coefficients throughout gives the same
criterion. The coefficient ring need not be commutative. These are ring
criteria, not arbitrary-semiring converses.

## Group subalgebra descent

For arbitrary types in independent universes, the hypotheses are

```lean
[Semiring R] [Group H] [Monoid M]
(j : H →* M) (hj : Function.Injective j)
[IsNoetherianRing (MonoidAlgebra R M)]
```

Then `MonoidAlgebra.isNoetherianRing_of_injective j hj` supplies
`IsNoetherianRing (MonoidAlgebra R H)`. In particular,
`MonoidAlgebra.isNoetherianRing_subgroup K` applies to every subgroup `K` of a
group with left-Noetherian group algebra. The subgroup need not be normal or
have finite index. There is no commutativity, nontriviality, additive-inverse,
finite-generation or cancellation hypothesis, and the target monoid need not
be a group.

Here `IsNoetherianRing A` means that the regular **left** module of `A` over
itself is Noetherian. It does not mean that the algebra is Noetherian as a
module over its coefficient semiring, nor does it concern only two-sided ideals.

## The coefficient projection

The [map module](../GroupRings/MonoidAlgebra/MapDomain.lean) uses the stock maps

- `i = MonoidAlgebra.mapDomainRingHom R j`, unchanged-coefficient pushforward;
- `P = MonoidAlgebra.comapDomainAddMonoidHom j hj`, additive coefficient pullback.

At `h : H`, the coefficient of `P a` is `a.coeff (j h)`, by
`MonoidAlgebra.coeff_comapDomain` and `Finsupp.comapDomain_apply`.
The representation bridge `MonoidAlgebra.comapDomain_mapDomain` gives
`P (i b) = b`. The substantive multiplication law is

```text
P (a * i b) = P a * b.
```

This is `MonoidAlgebra.comapDomain_mul_mapDomain`. Notice the order: the
coefficient of `a` stays to the left of that of `b`. The proof reduces the
right factor to single terms and uses

```text
m * j h = j k  ↔  m = j (k * h⁻¹).
```

Multiplication by the image of the inverse proves this equivalence even if
`M` has no cancellation. Thus no freeness of `R[M]` as an `R[H]`-module is
asserted. An absorbing point of a monoid, for example, may have a nontrivial
stabilizer under the image of `H`.

The projection is not generally multiplicative. Already for `R = ℤ`, the
trivial subgroup of the cyclic group of order two, and the nonidentity basis
term `g`, it sends `g` to zero but `g * g` to one. It must not be used as a
ring homomorphism in a surjective-ring-homomorphism descent theorem.

## Generic additive-retraction criterion

The [ring-theory module](../GroupRings/RingTheory/Noetherian.lean) works with any
semiring homomorphism `f : A →+* B` and additive map `E : B →+ A` satisfying

```text
E (f a) = a,
E (b * f a) = E b * a.
```

`RingHom.comap_map_eq_of_additive_retraction` proves
`Ideal.comap f (Ideal.map f J) = J` for every left ideal `J` of `A`.
For a generator `a ∈ J`, a left multiple `b * f a` projects to `E b * a ∈ J`.
Span induction retains these original ideal elements; it does not substitute
coefficient supports for ideal-generator labels. Extension therefore reflects
ideal inclusion. Transporting the ascending chain condition gives
`RingHom.isNoetherianRing_of_additive_retraction`.

The ring-homomorphism-retraction specialization is
`RingHom.comap_map_eq_of_leftInverse`. It agrees with the contraction equality
obtained from Mathlib's `Ideal.map_le_comap_of_inverse`; the general criterion
does not require the retraction to be a ring homomorphism.

## Related necessary conditions and boundaries

For any semiring and monoid, surjective augmentation also descends
left-Noetherianity to the coefficient semiring by Mathlib's generic
surjective-homomorphism theorem. Over a nontrivial ring,
`MonoidAlgebra.subgroup_fg_of_isNoetherianRing` additionally forces every
subgroup to be finitely generated. These are necessary conditions, not a
sufficient-condition converse for arbitrary noncommutative groups. The
commutative-group criterion above combines this necessity with the existing
commutative-monoid ascent.

The group-source hypothesis in subalgebra descent is essential: arbitrary
submonoids do not inherit Noetherianity of their algebras. Over a nonzero field,
`k + x*k[x,y]` is the monoid algebra of
`{(0,0)} ∪ {(a,b) ∈ ℕ² | 1 ≤ a}`. It sits inside the Noetherian algebra `k[x,y]`,
but the ideals generated successively by `x, xy, …, xyⁿ` form a strict ascending
chain. Conversely, the inclusion `ℤ × {0} ≤ ℤ²` illustrates why finite index
cannot be required in the group case.

The implementation reuses Mathlib's monoid-algebra and Finsupp maps,
coefficient multiplication laws, ideal spans and well-founded-order formulation
of Noetherianity. It introduces no new algebra, scalar action or projection.

## Finite-index subgroups

For a group `G`, a subgroup `H` and any coefficient semiring `R`,
`MonoidAlgebra.basisSubgroup H` is a basis of `R[G]` as a **left** `R[H]`-module.
Its index type is `Quotient (QuotientGroup.rightRel H)`, the right cosets `H * g`.
The action is the restriction of the regular left action:

```lean
letI := Module.compHom (MonoidAlgebra R G)
  (MonoidAlgebra.mapDomainRingHom R H.subtype)
```

The basis vector at `q` is `single q.out 1`. The finitely supported coordinates
are `MonoidAlgebra.subgroupRepr H f`; their coefficient formula is

```text
(subgroupRepr H f q).coeff h = f.coeff ((h : G) * q.out).
```

`subgroupRepr_symm_apply`, `subgroupCoord_sum` and `subgroupRepr_sum` give
reconstruction and both inverse identities. `subgroupCoord_mapDomain_mul`
expresses left scalar compatibility, without commuting any coefficients.
These laws apply even to the zero semiring and to nonnormal subgroups.

If `[H.FiniteIndex]`, `MonoidAlgebra.finite_subgroup H` supplies
`Module.Finite (MonoidAlgebra R H) (MonoidAlgebra R G)` for that same action.
When `[Ring R]`, `MonoidAlgebra.isNoetherianRing_iff_subgroup H` states

```text
IsNoetherianRing (MonoidAlgebra R G) ↔
  IsNoetherianRing (MonoidAlgebra R H).
```

Descent remains valid without finite index and over arbitrary semirings.
The reverse implication uses finite-module Noetherianity over a **ring**;
it is not a semiring ascent theorem. In particular, neither a commutative
coefficient assumption nor a normality assumption is hidden in the ascent.
No equality between numerical rank and subgroup index is asserted.

If the same inherited subgroup also has `[IsMulCommutative H]` and
`[Group.FG H]`, then
`MonoidAlgebra.isNoetherianRing_iff_of_finiteIndex_comm_fg H` gives

```text
IsNoetherianRing (MonoidAlgebra R G) ↔ IsNoetherianRing R.
```

The stock scoped commutativity promotion extends `H`'s given group structure;
no unrelated group or scalar structure is supplied. Neither `G`'s
commutativity nor `H`'s normality is required. The result composes the
finite-index equivalence with the FG commutative-monoid coefficient criterion.

The four cyclic compatibility results remain in the direct-import module
`GroupRings.MonoidAlgebra.CyclicNoetherian`: the integer criterion specializes
the FG monoid criterion, equivalences transport it, and a finite-index cyclic
subgroup specializes the finite-index FG commutative-subgroup result.
Products of the infinite cyclic group with finite groups use that chain.
The module also preserves its public Laurent Noetherian import; see
[credits](../CREDITS.md) for the earlier Laurent proof's formalization lineage.
