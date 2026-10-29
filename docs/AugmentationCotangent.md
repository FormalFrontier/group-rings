# Augmentation cotangents

For any unital ring `R` and monoid `M`,
`MonoidAlgebra.AugmentationCotangent R M` is the existing augmentation kernel
modulo its ordinary ideal product square. The quotient carries the coefficient
left `R`-action; no commutativity of the ring or monoid is required.
The quotient map kills exactly the square, and scalar multiplication by `r`
is induced by left multiplication by `single 1 r`.

`augmentationCotangentDelta R M m` is the class of `single m 1 - 1`.
Its scalar characteristic law identifies `r • delta m` with the class of
`single m r - single 1 r` for every coefficient and monoid element.

## Universal property

`augmentationCotangentEquiv` is a natural equivalence of sets

```text
(AugmentationCotangent R M →ₗ[R] V) ≃ (M →* Multiplicative V)
```

for any additive commutative group `V` with a left `R`-module structure.
It evaluates a linear map on `delta m`. The inverse sends `r • delta m`
to `r • (h m).toAdd`. This does not place an `R`-module structure on the
set of `R`-linear maps, and does not require a right action on `V`.
The coefficient, monoid, and target universes are independent.

The API includes `augmentationCotangentLift`, its coefficient-sum formula on
quotient representatives, and linear-map extensionality on the delta classes.
Naturality is formalized for target linear maps and monoid precomposition.
`augmentationCotangentMap` provides the induced cotangent map, with delta,
identity, and composition laws.

The proof uses the coefficient-linear extension of a character to the monoid
algebra. For kernel elements `x,y`, expansion of the character of a product
shows that this extension kills `x*y`. Induction on the ordinary ideal product
then allows descent to the quotient. Coefficients keep their original order.
This uses additive induction on ideal products, not a claim that the extension
is linear over the monoid algebra.

## Group specialization

For any group `G`, `augmentationCotangentTensorEquiv` is an `R`-linear equivalence

```text
AugmentationCotangent R G ≃ₗ[R] R ⊗[ℤ] Additive (Abelianization G).
```

It sends `delta g` to `1 ⊗ ab(g)`; its inverse sends `r ⊗ ab(g)` to
`r • delta g` for every `r,g`. The tensor product is over the integers,
not over `R`. The construction factors the delta character through the group
abelianization and uses representatives of that quotient to verify the inverse
laws. No freeness or torsion-freeness of the abelianization is assumed.

## Commutative comparison

The comparison lemma identifies the zero-class relation with that of
`Ideal.toCotangent` using the same kernel ideal and `pow_two`.
This is a relation bridge, not a linear equivalence with the stock cotangent
construction.

## Classical background and proof approach

For `R = ℤ`, the group specialization recovers the classical identification of
the integral augmentation ideal modulo its square with the additive
abelianization. The equivalence here allows any unital coefficient ring,
including noncommutative rings, and tensors the abelianization with `R` over
`ℤ`. It imposes no freeness or torsion-freeness assumptions.

The proof is a self-contained universal-property construction: extend a monoid
character coefficient-linearly, descend through the ordinary ideal-product
square, and then use group abelianization and the integer tensor product.
Brown's book below is cited for classical integral background; no proof from
that book or another published proof is followed.

## References

- Kenneth S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics,
  Springer, 1982. [doi:10.1007/978-1-4684-9327-6](https://doi.org/10.1007/978-1-4684-9327-6).
