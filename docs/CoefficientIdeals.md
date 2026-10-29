# Coefficient ideals and simultaneous change of coefficients and indices

## Ordinary left ideals

Import `GroupRings.MonoidAlgebra.CoefficientIdeals`. Let `R` and `S` be any
semirings and `M` any monoid, in independent universes. Write
`C = MonoidAlgebra.singleOneRingHom` and `F = MonoidAlgebra.mapRingHom M f`.
These are Mathlib's maps, not additional constructions.

For **every left ideal** `I : Ideal R`,

```text
x ∈ Ideal.map C I  ↔  ∀ m, x.coeff m ∈ I.
```

This is `MonoidAlgebra.mem_map_singleOneRingHom_iff`. Its single-term form
is `single_mem_map_singleOneRingHom_iff`. It does not assume two-sidedness:
for example, matrices with second column zero form a left ideal which need
not be two-sided. In the forward direction every convolution summand has
ordered coefficient product `a * b` with `b ∈ I`. In the reverse direction,
expand `x` as the sum of `single m 1 * C (x.coeff m)`.

For `I = RingHom.ker f`, `ker_mapRingHom` identifies the ideal with `ker F`.
`mapRingHom_eq_zero_iff` gives the all-coefficient vanishing criterion. This
works with noncommutative coefficients and arbitrary infinite monoids, including
a free monoid on two generators. Matrix reduction modulo a prime is a
surjective coefficient map with a proper nonzero kernel.

The additive-map statements `map_injective_iff` and `map_surjective_iff` reflect
these properties on any **nonempty index type**, without monoid assumptions.
Their forward directions reuse Mathlib's stronger existing APIs. Empty indices
would make reflection false. Zero kernel alone does not imply injectivity for
a semiring source: the natural map from natural numbers to the Boolean OR/AND
semiring has zero kernel but identifies all positive numbers.

## Coefficient quotients

Assume now **Ring R**, with **Semiring S** still sufficient. The kernel theorem
provides two-sidedness of `Ideal.map C (ker f)`. There is no public two-sidedness
or kernel-equality assumption.

- `quotientCoeffKerEquiv f hf`, for surjective `f`, has target `S[M]`.
- `quotientCoeffKerEquivRange f` always has target `F.rangeS`.

Their `_mk` formulas send every class `[x]` to `F x`; `_mk_single` sends
`[single m r]` to `single m (f r)` for every `m,r`. The `_unique` lemmas
characterize them by the formula on all classes. They compose
`Ideal.quotEquivOfEq` with Mathlib's first-isomorphism equivalence. They are
ring equivalences, not algebra equivalences over a noncommutative base.
For the inclusion of integers in rationals with trivial indices the range
target is the integers, not all rationals.

## Simultaneous maps

Import `GroupRings.MonoidAlgebra.MixedQuotient`. For a group `G`, arbitrary
monoid `M`, `f : R →+* S` and `φ : G →* M`, the map is the existing composite

```text
Ψ = (mapDomainRingHom S φ).comp (mapRingHom G f).
```

Let `J` be the left span of `single n 1 - 1` for `n : φ.ker`, and
`K = Ideal.map C (ker f)`. Then
`ker_mapDomainRingHom_comp_mapRingHom` proves `ker Ψ = J ⊔ K`.
No surjectivity, nontriviality, commutativity, cancellation or target-group
hypothesis is imposed; all four type universes are independent.

The proof factors through the surjective index map
`q : R[G] →+* R[MonoidHom.mrange φ]`. The intermediate still has **R**
coefficients, so ring-to-ring extension-contraction gives `K ⊔ ker q`.
Coefficient change follows this step, and the range inclusion into `S[M]`
is injective. The subgroup-relation theorem supplies `ker q`.
This avoids reconstructing collisions by support arguments. In particular,
`single g 1 - 1` can be in the mixed kernel when `φ g = 1` without its
individual coefficients belonging to `ker f`.

- If `f` is surjective, `quotientMixedKerEquivMrange` targets `S[range φ]`.
- If `φ` is also surjective, `quotientMixedKerEquivOfSurjective` targets `S[M]`.
- For arbitrary maps, `quotientMixedKerEquivRange` targets `Ψ.rangeS`.

Each equivalence has all-class and full basis-coefficient formulas and a
uniqueness lemma. Index surjectivity is sufficient, not necessary, for the
full-target result: a zero target coefficient semiring gives a singleton
algebra even with nonsurjective indices.

## Polynomial specialization

`GroupRings.Polynomial.CoefficientIdeals` uses the composite of
`Polynomial.toFinsuppIso R` with `AddMonoidAlgebra.toMultiplicative R ℕ`.
It preserves constants, sends coefficient `n` to coefficient `ofAdd n`, and
commutes with every coefficient homomorphism. The ideal membership and kernel
transport lemmas specialize to Mathlib's `Ideal.mem_map_C_iff` and
`Polynomial.ker_mapRingHom`, for arbitrary commutative coefficient semirings,
ideals, polynomials and independently universed semiring targets. The
transport itself already works with noncommutative semiring coefficients.
