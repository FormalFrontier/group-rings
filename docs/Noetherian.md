# Left-Noetherian group subalgebras

Import `GroupRings.MonoidAlgebra.Noetherian` or the aggregate `GroupRings`.
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
sufficient-condition converse.

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
