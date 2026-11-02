# Jacobson radicals of locally finite p-group algebras

Import `GroupRings.MonoidAlgebra.Jacobson`, or the aggregate `GroupRings`.
The module publicly imports
`GroupRings.MonoidAlgebra.AugmentationNilpotence.LocallyFinite` for the
underlying elementwise nilness theorem.

Throughout this guide, `R[G]` means the canonical `MonoidAlgebra R G`, and
`augmentation R G : R[G] →+* R` is the coefficient-sum homomorphism.
`Ring.jacobson R` denotes the two-sided Jacobson radical of a ring, represented
as an `Ideal R`; it is not the radical of a separately chosen left ideal.

## Hypotheses

All four radical theorems use the following data:

- any unital ring `R`, possibly noncommutative or zero;
- any group `G`, in a universe independent of that of `R`;
- a prime natural number `p`, with the equality `(p : R) = 0`;
- `IsPGroup p G`;
- `∀ s : Finset G, Finite (Subgroup.closure (s : Set G))`.

The last hypothesis says that every finite subset of `G` generates a finite
subgroup. The group need not itself be finite, finitely generated or abelian.
No `CharP` or nontriviality hypothesis is imposed on the coefficient ring.

## Radical and membership

`MonoidAlgebra.jacobson_eq_comap_augmentation` gives

```text
Ring.jacobson R[G] = Ideal.comap (augmentation R G) (Ring.jacobson R).
```

Thus the radical is determined by augmentation, rather than by requiring every
coefficient to belong to the coefficient radical. The membership form is
`MonoidAlgebra.mem_jacobson_iff_augmentation_mem`:

```text
x ∈ Ring.jacobson R[G] ↔ augmentation R G x ∈ Ring.jacobson R.
```

For a finite sum of basis terms, augmentation is the sum of the coefficients.
The criterion therefore concerns that sum, including cancellation among its
terms.

## Basis terms and coefficient inclusion

For arbitrary `g : G` and `r : R`,
`MonoidAlgebra.single_mem_jacobson_iff` states

```text
single g r ∈ Ring.jacobson R[G] ↔ r ∈ Ring.jacobson R.
```

The coefficient need not be central. Taking `g = 1` gives the criterion for
canonical coefficient inclusion, whose value at `r` is `single 1 r`.

## Zero coefficient radical

Given `hJ : Ring.jacobson R = ⊥`, apply
`MonoidAlgebra.jacobson_eq_ker_augmentation_of_jacobson_eq_bot` to obtain

```text
Ring.jacobson R[G] = RingHom.ker (augmentation R G).
```

This hypothesis is vanishing of the coefficient ring's Jacobson radical; it
is not a field assumption and does not require the coefficient ring to be
nonzero or commutative.

## Elementwise nilness, not ideal nilpotence

The [locally finite nilness theorem](../GroupRings/MonoidAlgebra/AugmentationNilpotence/LocallyFinite.lean)
says that each augmentation-zero element is nilpotent. Its exponent may depend
on the element. It asserts neither a common exponent nor a vanishing power of
the entire augmentation ideal.

A nilpotent element `x` has `1 + x` invertible. Applying this to every element
of the augmentation kernel gives a quasiregular two-sided ideal, hence an ideal
contained in the Jacobson radical. Augmentation is surjective, and the
surjective Jacobson-radical correspondence then identifies its radical
preimage. This uses the quasiregular-ideal criterion in
`GeneralLinearGroups.QuasiregularIdeal` and Mathlib's Jacobson-radical API.

The [finite-group nilpotence results](AugmentationNilpotence.md) provide uniform
ideal-power bounds under finite-group hypotheses. Those stronger bounds are
not asserted here for an arbitrary locally finite group.
