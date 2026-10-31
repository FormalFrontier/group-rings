# group-rings

Monoid-algebra single-term units and augmentation-kernel bases, group algebras with
explicit free abelian coordinates, and algebraic finite-abelian character
convolution, formalized in Lean.

Authors: Formal Frontier Agents

License: [Apache-2.0](LICENSE) for original project contributions. Dependencies
retain their own licenses and contributor notices.

This README describes the API in this checkout. Use an exact official release
revision when pinning a dependency; [formalization.yaml](formalization.yaml)
records scope and attribution, not a live release registry.

## Headline results

- **Projectivity from coefficient projectivity.** For a finite group `G` whose
  order is a unit in any possibly noncommutative or zero semiring `R`, a given
  `R[G]`-module that is projective under its canonical coefficient restriction
  is projective over `R[G]`. Additive commutative monoids and independent
  coefficient, group and module universes suffice. See
  [Projective.lean](GroupRings/MonoidAlgebra/Projective.lean).

- **Canonical representations of given modules.** Over any possibly
  noncommutative or zero semiring `R` and any monoid `M`, a given unital
  `R[M]`-module has a representation on its original carrier with exactly the
  canonical coefficient restriction. Original monoid-algebra linear maps are
  additively equivalent to coefficient-linear intertwiners between these
  representations, without changing their values; the modules may be arbitrary
  additive commutative monoids in independent universes. Packaging preserves
  identity and composition, and the equivalence reflects existence of lifts
  `q.comp f = h` for original module maps, without assuming surjectivity or
  projectivity. See
  [ModuleRepresentationEquiv.lean](GroupRings/MonoidAlgebra/ModuleRepresentationEquiv.lean).
  For commutative coefficients the inverse agrees with Mathlib's Hom
  correspondence through both canonical `asModuleEquiv` transports; the
  [representation construction](GroupRings/MonoidAlgebra/ModuleRepresentation.lean)
  also agrees pointwise with Mathlib's scalar-restriction constructions.
  For a semisimple module of a finite `p`-group algebra over any ring with
  prime `p = 0`, this canonical representation is trivial.

- **Semisimplicity under a nilpotent ideal action.** For arbitrary rings `S`,
  `A`, a unital map `φ : S →+* A` surjective modulo a two-sided ideal `I`,
  and any given `A`-module `V` with `∃ n, I^n ≤ Module.annihilator A V`,
  semisimplicity over `A` is equivalent to `I` annihilating `V` together with
  semisimplicity under the exact restriction `Module.compHom V φ`. This is
  nilpotence of the action, not necessarily of the ideal; the exponent may be
  zero. The ideal action also lies in the module's Jacobson radical, and the
  same characterization holds under that weaker radical condition. See
  [Semisimple.lean](GroupRings/RingTheory/Ideal/Semisimple.lean).
  For any ring `R`, prime `p` with `(p : R) = 0`, finite `p`-group `G` and
  given `R[G]`-module, semisimplicity is equivalent to canonical coefficient
  semisimplicity **and** trivial canonical group action. In particular, every
  group symbol fixes every vector of a semisimple module. See
  [SemisimpleModules.lean](GroupRings/MonoidAlgebra/SemisimpleModules.lean).
  Neither result assumes commutativity, nontriviality, finite generation or
  finite length, and the scalar rings and module have independent universes.

- **Scalar restriction and module length.** For any rings `S`, `A`, homomorphism
  `φ : S →+* A`, and given left `A`-module `V`, let `I` be a two-sided ideal
  with `∃ n, I^n ≤ Module.annihilator A V` and surjective canonical map
  `S → A/I`. Noetherianity and Artinianity are each equivalent over `A` and
  the exact restriction `Module.compHom V φ`; their composition lengths agree
  in `ℕ∞`, including infinity. In particular this holds for nilpotent `I`.
  The map `φ` need not be injective, split, surjective itself or have central
  image. See [ScalarRestriction.lean](GroupRings/RingTheory/Ideal/ScalarRestriction.lean).
  For any ring `R`, prime `p` with `(p : R) = 0`, finite `p`-group `G`, and
  arbitrary given `R[G]`-module, all three comparisons hold with its canonical
  coefficient restriction to `R`. There is no field, commutativity, finite
  generation or finite-length assumption. See
  [ModuleFiniteness.lean](GroupRings/MonoidAlgebra/ModuleFiniteness.lean).
  Only annihilated layers have equal submodule lattices, not generally the
  whole module. The length is relative to the scalar ring, not an underlying
  field dimension.

- **Detection of module maps.** Let `R` be any possibly noncommutative or zero
  ring, `p` a prime with `(p : R) = 0`, and `G` a finite `p`-group. Every
  `R[G]`-linear map is injective exactly when its canonical fixed-vector map is
  injective, and surjective exactly when its canonical coinvariant map is
  surjective. The modules may lie in independent universes and need not be
  finitely generated. Fixed vectors are the augmentation ideal's common
  annihilator with the canonical coefficient restriction; coinvariants are
  the original quotient by `I • ⊤`. See
  [ModuleDetection.lean](GroupRings/MonoidAlgebra/ModuleDetection.lean).
  The [general ideal-module results](GroupRings/RingTheory/Ideal/ModuleDetection.lean)
  give injectivity detection for nilpotent two-sided ideals over semirings
  acting on additive groups, and surjectivity detection for nilpotent left
  ideals over rings. Nilpotent Nakayama itself allows arbitrary semimodules.
  Neither individual functor is asserted to reflect all isomorphisms.

- **Crossed maps and the full augmentation ideal.** For any ring `R`, monoid `M`,
  and unital left `R[M]`-module `V`, the `R[M]`-linear maps from the full
  augmentation ideal `I` to `V` are additively equivalent to normalized maps
  `z : M → V` satisfying `z(mn) = z(m) + [m] • z(n)`, with the canonical
  action `[m] • v`. The forward map is `z(m) = F([m] - 1)`. See
  [AugmentationCrossedUniversal.lean](GroupRings/MonoidAlgebra/AugmentationCrossedUniversal.lean).

- **Simple modules of finite `p`-group algebras.** For any possibly
  noncommutative or zero ring `R`, prime `p` with `(p : R) = 0`, finite
  `p`-group `G` and unital left `R[G]`-module `V`, simplicity over `R[G]`
  is equivalent to simplicity over `R` under canonical coefficient
  restriction. A simple module has augmentation action: every group basis
  element fixes every vector. No finiteness assumption on `V`, field or
  additional nontriviality hypothesis is needed. The characterization of
  augmentation action by trivial monoid action holds over any semiring.
  See the [simple-module guide](docs/SimpleModules.md) and
  [module](GroupRings/MonoidAlgebra/SimpleModules.lean).

- **Common annihilators and fixed vectors.** If one power of an ordinary left
  ideal over any semiring annihilates a nontrivial semimodule, there is a
  nonzero vector killed by the whole ideal. Two-sided ideals have a canonical
  common-annihilator submodule, agreeing with commutative set torsion. For a
  finite `p`-group over any possibly noncommutative ring with prime `p = 0`,
  every nontrivial unital group-algebra module has a nonzero vector fixed by
  all canonical group symbols. No field, coefficient commutativity, `CharP`,
  finite generation, dimension or finite-module hypothesis is needed. See the
  [common-annihilator and fixed-vector guide](docs/FixedVectors.md).

- **Cotangent covariance and products.** For arbitrary unital rings, coefficient
  change is semilinear and commutes with monoid covariance. The group comparison
  with `R ⊗[ℤ] Additive (Abelianization G)` is natural for both variables.
  For any two monoids, `Q_R(M × N) ≃ₗ[R] Q_R(M) × Q_R(N)` via projections and
  the sum of inclusions. See the [cotangent guide](docs/AugmentationCotangent.md)
  and `MonoidAlgebra.augmentationCotangentProdEquiv`.


- **Augmentation nilpotence and finite `p`-groups.** For a prime `p`, any
  possibly noncommutative ring `R` with `(p : R) = 0`, and a finite `p`-group
  `G`, the [augmentation kernel has zero `Nat.card G`-th power](GroupRings/MonoidAlgebra/AugmentationNilpotence/Finite.lean).
  Thus every mixed ordered product of that length vanishes, including over
  the zero coefficient ring. Conversely, for **nontrivial** `R` and **any**
  group `G`, nilpotence implies `∃ k, ∀ g : G, g ^ (p ^ k) = 1`, hence
  `IsPGroup p G`. This gives the finite-group iff. The supporting left-ideal
  API over **any semiring** identifies zero `n`-th powers with vanishing of
  all length-`n` ordered products, including degree zero. See the
  [augmentation-nilpotence guide](docs/AugmentationNilpotence.md).

- **Augmentation cotangents.** For any unital ring `R`, monoid `M` and left
  `R`-module `V`, linear maps from `I/I²` to `V` are naturally equivalent, as a
  **set**, to monoid homomorphisms `M →* Multiplicative V`. For a group `G`,
  there is an **`R`-linear equivalence**
  `I/I² ≃ₗ[R] R ⊗[ℤ] Additive (Abelianization G)`.
  Here `I` is the augmentation ideal and `I²` its ordinary ideal product square.
  No commutativity of `R` or `M`, or freeness of `G` or its abelianization, is
  assumed. See the [universal-property module](GroupRings/MonoidAlgebra/AugmentationCotangent/Universal.lean),
  [group tensor module](GroupRings/MonoidAlgebra/AugmentationCotangent/Tensor.lean)
  and [augmentation-cotangent guide](docs/AugmentationCotangent.md).

- **Coefficient ideals and kernels.** For any semiring `R`, monoid `M`, and
  ordinary **left** ideal `I`, extension along the constants map consists
  exactly of elements whose every coefficient belongs to `I`. Thus for any
  homomorphism `f : R →+* S` between independently universed semirings,
  `ker (mapRingHom M f) = Ideal.map singleOneRingHom (ker f)`, with no
  commutativity, inverses, finiteness, nontriviality or surjectivity assumption.
  With **Ring R**, **Semiring S** and surjective `f`, the quotient is `S[M]`;
  without surjectivity it is the map's range subsemiring. The
  [coefficient-ideal module](GroupRings/MonoidAlgebra/CoefficientIdeals.lean)
  supplies membership, all-basis, class and uniqueness formulas. The
  [polynomial transport](GroupRings/Polynomial/CoefficientIdeals.lean) preserves
  all coefficients, constants, ideals and coefficient change.

- **Simultaneous coefficient/index kernels.** For **Ring R**, **Semiring S**,
  **Group G**, **Monoid M**, `f : R →+* S` and `φ : G →* M`, the
  [mixed-map kernel](GroupRings/MonoidAlgebra/MixedQuotient.lean) is the sum of
  the left span of `single n 1 - 1` for `n ∈ φ.ker` and the extended coefficient
  kernel. Neither map need be surjective, and `M` need not be cancellative or
  a group. Under surjective `f`, the quotient is `S[MonoidHom.mrange φ]`;
  if `φ` is also surjective it is `S[M]`. For arbitrary maps the target is the
  composite's range subsemiring. No nontriviality or commutativity is assumed;
  all four universes are independent. The [guide](docs/CoefficientIdeals.md)
  explains the factorization and collision boundary.

- **Subgroup-coset bases.** For any semiring `R`, group `G` and subgroup `H`,
  `R[G]` has a basis as a left `R[H]`-module indexed by right cosets `H * g`.
  Its vectors are single terms at chosen representatives; the coordinate at
  `q` has coefficient `f.coeff (h * q.out)` at `h : H`. The
  [subgroup-basis module](GroupRings/MonoidAlgebra/SubgroupBasis.lean) provides
  finitely supported coordinates, reconstruction and left scalar compatibility.
  Finite index gives `Module.Finite` over arbitrary semirings, including zero
  and noncommutative ones. For **ring** coefficients, finite index gives
  `IsNoetherianRing (R[G]) ↔ IsNoetherianRing (R[H])`. No normality, finite-group
  or numerical-rank hypothesis is imposed.

- **Left-Noetherian group subalgebras.** For any semiring `R`, group `H`, monoid
  `M` and injective `j : H →* M` in independent universes, left-Noetherianity of
  `R[M]` implies that of `R[H]`. Thus every subgroup algebra of a left-Noetherian
  group algebra is left-Noetherian, without finite index or normality. No
  commutativity, nontriviality, additive inverses, cancellation or target-group
  assumption is needed. The [Noetherian guide](docs/Noetherian.md) describes the
  additive right retraction, ideal extension-contraction and the distinction
  between right compatibility and ordinary regular-left Noetherianity.

- **Left-Noetherian necessary conditions.** If `R[M]` is left-Noetherian, then
  `R` is left-Noetherian, for any semiring `R` and monoid `M`: augmentation is
  surjective, so Mathlib's generic surjective-homomorphism theorem applies.
  Over a **nontrivial**, possibly noncommutative ring `R`, left-Noetherianity
  of `R[G]` implies that **every** subgroup of `G` is finitely generated.
  This uses the algebra as a left module over itself, not over `R`.
  See the [necessary-condition module](GroupRings/MonoidAlgebra/Noetherian.lean)
  and [public-import client](tests/GroupRingsTest/NoetherianClient.lean).
  No converse for arbitrary groups is asserted.

- **Cyclic and finite-index Noetherianity.** For every ring `R`, including
  noncommutative and zero rings, `R[Multiplicative ℤ]` is left-Noetherian iff
  `R` is. An equivalence with the infinite cyclic group, or a finite-index
  infinite cyclic subgroup, gives the same criterion, without normality.
  This includes products with finite groups. Import
  `GroupRings.MonoidAlgebra.CyclicNoetherian` directly; the root does not
  re-export it. Laurent ascent comes from `multivariate-polynomials`;
  see [credits](CREDITS.md).

- **Normal-subgroup quotients.** For any ring `R`, group `G` and normal subgroup
  `N`, the canonical index map identifies `R[G/N]` with the quotient of `R[G]`
  by the left span of `single n 1 - 1`. The equivalence preserves every
  coefficient. A unital ring homomorphism into any semiring factors uniquely
  exactly when it sends all `single n 1` to one. No commutativity,
  nontriviality or finiteness is assumed; see the [quotient guide](docs/Quotient.md).

- **Kernel and range quotients.** For any group-to-monoid homomorphism `φ`,
  the unchanged-coefficient map on group rings has kernel the left span of
  `single n 1 - 1` for `n ∈ φ.ker`. The quotient is canonically ring-equivalent
  to the algebra of the range submonoid, with full coefficient formulas and
  unique factorization into any semiring. Surjective `φ` also gives the whole
  target algebra. The coefficient ring may be noncommutative or zero, and no
  group structure on the target is assumed; see the
  [kernel and range guide](docs/KernelRange.md).

- **Coefficient change.** For any unital homomorphism `φ : R →+* S` from
  a possibly noncommutative ring to a semiring, and any monoid `M`,
  [coefficient change](GroupRings/MonoidAlgebra/CoefficientChange.lean)
  maps the augmentation ideal of `R[M]` onto that of `S[M]` as an ideal.
  The homomorphism need not be surjective. Naturality and the kernel
  preimage formula hold for arbitrary semiring coefficients.

- **Subgroup augmentation ideals.** For any possibly noncommutative ring `R`,
  group `G` and subgroup `H`, the [left ideal of subgroup differences](GroupRings/MonoidAlgebra/SubgroupIdeals.lean)
  consists exactly of elements with zero coefficient sums on every left coset
  `gH`. The coset-sum map itself needs only a semiring. Over a **nontrivial**
  ring, these ideals reflect subgroup membership and inclusion, and are
  two-sided exactly when `H` is normal. Characteristic membership, forward
  inclusion and normality implying two-sidedness also allow the zero ring.
  No commutativity or finiteness is assumed; the [guide](docs/SubgroupIdeals.md)
  explains the coefficient module, hypotheses and nonnormal matrix-ring example.

- **Finite generation of subgroup ideals.** Over any ring, a finitely generated
  subgroup gives a [finitely generated left group-ring ideal](GroupRings/MonoidAlgebra/SubgroupIdealsFG.lean).
  Over a **nontrivial** ring the converse holds, without normality or
  commutativity. In particular, the augmentation kernel is finitely generated
  as a left ideal exactly when the group is finitely generated. The forward
  implication allows the zero ring. This is finite generation over `R[G]`,
  not over `R`; the [public-import client](tests/GroupRingsTest/SubgroupIdealsFGClient.lean)
  illustrates matrix coefficients, an infinite cyclic group and the zero-ring
  boundary for an infinite-rank free abelian group.

- **Single-term units.** For any semiring `R` and monoid `M` in independent
  universes, a unit `single m r` has a unit coefficient `r`, even when `R` is
  trivial. Over a **nontrivial** semiring, the
  [basis embedding reflects units](GroupRings/MonoidAlgebra/Units.lean), and
  `IsUnit (single m r) ↔ IsUnit r ∧ IsUnit m`. No ring, commutativity, group,
  cancellation, domain or finiteness hypothesis is required. This classifies
  single terms, not units represented by arbitrary finite sums.
- **Augmentation kernel generators.** For any possibly noncommutative ring `R`
  and any monoid `M` in independent universes, the
  [augmentation kernel](GroupRings/MonoidAlgebra/Augmentation.lean) in
  `MonoidAlgebra R M` is the **left** ideal generated by `single m 1 - 1`.
  The coefficient-sum augmentation is a ring homomorphism already over any
  semiring. Its coefficient-sum and single-term evaluation laws give its public
  API. Neither commutativity, inverses, finiteness nor nontriviality is assumed.
  A [monoid generating set](GroupRings/MonoidAlgebra/AugmentationGenerators.lean)
  `S` already suffices: the kernel is the left span of `single s 1 - 1` for
  `s ∈ S` when `Submonoid.closure S = ⊤`. For a group, the weaker hypothesis
  `Subgroup.closure S = ⊤` suffices for the same span; no normal closure is used.
- **Augmentation-kernel coefficient basis.** For any possibly noncommutative
  ring `R` and monoid `M` in independent universes,
  [`MonoidAlgebra.augmentationKerBasis`](GroupRings/MonoidAlgebra/AugmentationBasis.lean)
  is a basis of `(RingHom.ker (MonoidAlgebra.augmentation R M)).restrictScalars R`
  over the **left coefficient ring `R`**, not over `R[M]`. Its index type is
  `{m : M // m ≠ 1}`, its vector is `single m 1 - 1`, and the coordinate of a
  kernel element at `m` is its coefficient at `m`. No group, commutativity,
  cancellation, finiteness, nontriviality or decidable-equality premise is added.
  The zero ring and singleton monoids are allowed. The generic engine
  [`Finsupp.kerLsumEquiv`](GroupRings/LinearAlgebra/Finsupp/SumKernel.lean)
  works for any semiring acting on an additive commutative group: restrict away
  from a chosen point, and invert by extension minus the coefficient sum at that
  point. A semiring coefficient basis assertion would be false in general.
- **Laurent coordinates.** For a commutative semiring `A`, additive commutative
  group `G`, and *supplied* equivalence `G ≃+ (σ →₀ ℤ)`, the
  [coordinate equivalence](GroupRings/FreeAbelian/LaurentPolynomial.lean#L35)
  identifies `MonoidAlgebra A (Multiplicative G)` with
  `MvLaurentPolynomial σ A = AddMonoidAlgebra A (σ →₀ ℤ)`. The
  [forward](GroupRings/FreeAbelian/LaurentPolynomial.lean#L44) and
  [inverse](GroupRings/FreeAbelian/LaurentPolynomial.lean#L60) basis formulas
  give the image of every single term. The Laurent abbreviation itself needs
  only `[Semiring A]`; no choice of coordinates is proved. Specializing along
  `FreeAbelianGroup.equivFinsupp` gives the
  [canonical equivalence](GroupRings/FreeAbelian/LaurentPolynomial.lean#L76),
  its [forward](GroupRings/FreeAbelian/LaurentPolynomial.lean#L84) and
  [inverse](GroupRings/FreeAbelian/LaurentPolynomial.lean#L95) single-term laws,
  and a [generator simp law](GroupRings/FreeAbelian/LaurentPolynomial.lean#L106)
  at priority 1100. Each exponent has finite support; `σ` itself can be empty
  or infinite, and negative exponents and the zero commutative semiring are
  permitted. This does not establish projective-module freeness or K-theory.
- **Field-valued character independence and bases.** Characters of an additive
  commutative `G` have [linearly independent evaluations](GroupRings/FiniteAbelian/RightConvolution.lean#L43)
  over any field, even when `G` is infinite. A finite `G` has finitely many
  characters over any field; enough roots of unity of exponent
  `Monoid.exponent (Multiplicative G)` then yield the
  [cardinality theorem](GroupRings/FiniteAbelian/RightConvolution.lean#L66)
  and [evaluation basis](GroupRings/FiniteAbelian/RightConvolution.lean#L74).
- **Right convolution, eigenvalues and rank.** With `[Fintype G]`, the
  [right-convolution matrix](GroupRings/FiniteAbelian/RightConvolution.lean#L105)
  has entries `f (-sigma + tau)` and positive-character eigenvalues
  `∑ x, f x * psi x` without a roots assumption for its
  [eigenvector law](GroupRings/FiniteAbelian/RightConvolution.lean#L113).
  Under enough roots it admits [diagonalization](GroupRings/FiniteAbelian/RightConvolution.lean#L137)
  and a [Nat.card rank formula](GroupRings/FiniteAbelian/RightConvolution.lean#L161).
  The [Fourier guide](docs/FiniteAbelianRightConvolution.md) gives exact
  hypotheses, the positive sign and client examples.

## Mathematical scope

`MvLaurentPolynomial σ A` is an abbreviation for
`AddMonoidAlgebra A (σ →₀ ℤ)`: a monomial has a finitely supported vector of
integer exponents. The variable type itself may be empty, finite or infinite;
negative exponents are allowed. This model needs only a semiring `A`, without
commutativity or nontriviality.

For a commutative coefficient semiring `A`, an additive commutative group `G`,
and supplied coordinates `e : G ≃+ (σ →₀ ℤ)`, the API constructs

```lean
MonoidAlgebra A (Multiplicative G) ≃ₐ[A] MvLaurentPolynomial σ A
```

It first reverses mathlib's additive-to-multiplicative group-algebra equivalence,
then transports the exponent group along `e`. The canonical specialization takes
`G = FreeAbelianGroup σ` and uses `FreeAbelianGroup.equivFinsupp σ`. The coefficient,
group and index universes are independent in the supplied-coordinate form.

The API requires no decidable equality, finite generation, field, domain, ring or
nonzero-coefficient assumption. Its equivalences also apply to the zero
commutative semiring. It does not choose coordinates from an unbundled existential
freeness assertion.

This library does **not** prove projective-module freeness, Laurent-PID structure,
Quillen–Suslin or Bass–Quillen, stable freeness or K-theory. An algebra equivalence
alone does not prove projectives free.

Separately, for an additive commutative group `G` and field `K` (in independent
universes), evaluations by `AddChar G K` are linearly independent without a
finite-group or enough-roots hypothesis. For finite `G`, character finiteness
holds over any field. If the field has enough roots of unity of exponent
`Monoid.exponent (Multiplicative G)`, character evaluations give a basis of
`G → K`. For `[Fintype G]`, right convolution has matrix entry
`f (-sigma + tau)` and character eigenvalue `∑ x, f x * psi x`; its eigenvector
law needs no enough-roots assumption. Under enough roots, the character basis
diagonalizes convolution and its rank is the `Nat.card` of characters with
nonzero eigenvalue. This does not identify convolution with a group-algebra
operator or assert a nonabelian Fourier basis.

For any semiring `R` and monoid `M`, `MonoidAlgebra.augmentation R M` sends an
algebra element to the sum of its coefficients. If `R` is a ring, its kernel is
`Ideal.span (Set.range (fun m : M => MonoidAlgebra.single m (1 : R) - 1))`.
Here `Ideal.span` is a left ideal: the coefficient expansion uses
`single 1 r * (single m 1 - 1)`, with the coefficient on the left. The
[augmentation client](tests/GroupRingsTest/AugmentationClient.lean) independently
exhibits a nonzero kernel element over `ℤ` and the natural-number monoid, and
uses the span theorem with arbitrary left coefficients and monoid indices.
The [generating-set client](tests/GroupRingsTest/AugmentationGeneratorsClient.lean)
uses two generators of `FreeMonoid Bool` with noncommutative matrix coefficients,
obtains finite generation directly from finite image and `Submodule.fg_span`,
and checks that the infinite cyclic group's inverse difference lies in the span
of the positive generator difference despite failure of monoid generation.
The [coefficient-basis client](tests/GroupRingsTest/AugmentationBasisClient.lean)
uses the vector and coordinate laws over a matrix ring and `Multiplicative ℕ`,
distinguishing left scalar multiplication from right multiplication. The
semiring-level `sumCoords_basis_apply` and `ker_augmentation_restrictScalars`
bridges identify Mathlib's coordinate sum with augmentation.

The [single-term client](tests/GroupRingsTest/SingleUnitsClient.lean) constructs
an independent nonidentity unit over `ℕ` at the positive generator of
`Multiplicative ℤ`, checking its inverse directly from multiplication laws.
It also uses the single-term criterion to rule out invertibility of the basis
term at `2` in `MonoidAlgebra ℕ ℕ`, whose index monoid is not a group. The zero
coefficient semiring explains the nontriviality hypothesis for index reflection:
its monoid algebra is trivial, so every basis image is a unit regardless of its
index.

## Using the library

Add the dependency to your `lakefile.toml`:

```toml
[[require]]
name = "group-rings"
git = "https://github.com/FormalFrontier/group-rings.git"
rev = "main"
```

GitHub `main` contains only reviewed releases. Lake resolves a release when you
add or update the dependency; `lake-manifest.json` locks that commit until the
next update. For a specific release, replace `main` with its full commit from
that history. Libraries used together must share a compatible Lean toolchain
and the same mathlib revision.

Import `GroupRings`, or one of its leaf modules:

| Module | Contents |
| --- | --- |
| `GroupRings.MonoidAlgebra.SubgroupIdeals` | Left coset coefficient sums and subgroup left ideals, inclusion and normality. |
| `GroupRings.MonoidAlgebra.SubgroupIdealsFG` | Finite generation of subgroup left ideals and augmentation kernels. |
| `GroupRings.MonoidAlgebra.SubgroupBasis` | Right-coset bases, left subgroup-algebra coordinates and finite-index module finiteness over semirings. |
| `GroupRings.MonoidAlgebra.Noetherian` | Left-Noetherian group-subalgebra descent, finite-index equivalence over rings and necessary conditions. |
| `GroupRings.MonoidAlgebra.CyclicNoetherian` | Direct import: cyclic coefficient criterion, group-equivalence and finite-index transport, finite-group products. |
| `GroupRings.MonoidAlgebra.MapDomain` | Coefficient projection retracts pushforward and commutes with right multiplication by a group image. |
| `GroupRings.RingTheory.Noetherian` | Ideal extension-contraction and left-Noetherian descent for additive right retractions. |
| `GroupRings.MonoidAlgebra.Units` | Single-term units and reflection by the basis embedding. |
| `GroupRings.MonoidAlgebra.AugmentationNilpotence` | Uniform group exponents from augmentation nilpotence over nontrivial rings of prime characteristic. |
| `GroupRings.MonoidAlgebra.AugmentationNilpotence.Finite` | Exact cardinality bound for finite p-groups over any ring with p=0, and the finite-group criterion. |
| `GroupRings.RingTheory.Ideal.Annihilator` | Uniformly nilpotent actions, nonzero common vectors and two-sided-ideal annihilator submodules. |
| `GroupRings.MonoidAlgebra.FixedVectors` | Augmentation annihilation iff canonical fixedness, and nonzero fixed vectors for finite p-group modules. |
| `GroupRings.MonoidAlgebra.ModuleRepresentation` | Canonical representations and faithful intertwiner packaging on given modules over any semiring. |
| `GroupRings.MonoidAlgebra.ModuleRepresentationEquiv` | Additive Hom correspondence on original modules, inverse evaluation, lift reflection and the commutative Mathlib comparison. |
| `GroupRings.MonoidAlgebra.ModuleMaps` | Coefficient-and-basis criterion for linearity over any monoid algebra. |
| `GroupRings.MonoidAlgebra.ModuleDetection` | Canonical fixed-vector and coinvariant maps, their characteristic laws, and detection for finite p-group algebras. |
| `GroupRings.RingTheory.Ideal.ModuleDetection` | Nilpotent Nakayama and detection of injectivity and surjectivity by nilpotent ideals. |
| `GroupRings.RingTheory.Ideal.ScalarRestriction` | Uniform ideal-action induction; quotient-surjective restriction preserves both chain conditions and composition length, including infinity. |
| `GroupRings.MonoidAlgebra.ModuleFiniteness` | Noetherianity, Artinianity and length under canonical coefficient restriction for finite p-group algebras. |
| `GroupRings.RingTheory.Ideal.Semisimple` | Nilpotent ideal actions on semisimple modules vanish; canonical restriction and module-radical semisimplicity criteria. |
| `GroupRings.MonoidAlgebra.SemisimpleModules` | Semisimplicity for finite p-group algebras iff canonical coefficient semisimplicity and trivial group action. |
| `GroupRings.RingTheory.Ideal.Powers` | Ordered mixed products, ideal-power iteration and extension bounds over semirings. |
| `GroupRings.MonoidAlgebra.Augmentation` | Coefficient-sum augmentation and left-ideal kernel generators. |
| `GroupRings.MonoidAlgebra.CoefficientIdeals` | Ordinary left coefficient ideals, coefficient kernels and quotient equivalences. |
| `GroupRings.MonoidAlgebra.MixedQuotient` | Simultaneous coefficient/index kernels and range or surjective quotients. |
| `GroupRings.Polynomial.CoefficientIdeals` | Constant, coefficient, ideal and kernel transport from polynomials. |
| `GroupRings.MonoidAlgebra.CoefficientChange` | Naturality, kernel preimages and ideal images under coefficient change. |
| `GroupRings.MonoidAlgebra.AugmentationGenerators` | Kernel generators from monoid or subgroup generating sets. |
| `GroupRings.RingTheory.Ideal.MonoidHom` | Difference-membership propagation through monoid and subgroup closure in any ring's left ideals. |
| `GroupRings.LinearAlgebra.Finsupp.SumKernel` | Pointed coefficient-sum kernel equivalence for modules over semirings. |
| `GroupRings.MonoidAlgebra.AugmentationBasis` | Left coefficient-module basis and its coordinate and vector laws. |
| `GroupRings.FreeAbelian.LaurentPolynomial` | Laurent coordinates and free-abelian specialization. |
| `GroupRings.FiniteAbelian.RightConvolution` | Character bases and Fourier convolution. |

These are native Lean modules with deliberate public exports; no private import
is required by consumers.

| Declaration | Purpose |
| --- | --- |
| `MonoidAlgebra.moduleCoefficientModule_apply` | The canonical coefficient action is the action of `single 1 r` in the given module, over any semiring and monoid. |
| `MonoidAlgebra.moduleCoefficientModule_isScalarTower` | A locally installable scalar tower for the ordinary coefficientwise action on `R[M]` and the canonical coefficient restriction on the given module. |
| `MonoidAlgebra.cosetSum`, `cosetSum_single`, `cosetSum_apply` | Coefficient-linear coset projection, basis simp law and finite-support formula. |
| `MonoidAlgebra.mem_span_subgroup_iff` | Subgroup left-span membership iff every left-coset coefficient sum vanishes, over any ring. |
| `MonoidAlgebra.single_sub_one_mem_span_subgroup_iff`, `span_subgroup_le_iff` | Over a nontrivial ring, reflect subgroup membership and inclusion. |
| `MonoidAlgebra.span_subgroup_isTwoSided`, `span_subgroup_isTwoSided_iff` | Normality implies two-sidedness over any ring; the converse needs nontriviality. |
| `MonoidAlgebra.span_subgroup_fg_of_fg`, `span_subgroup_fg_iff` | Subgroup FG implies left-ideal FG over any ring; equivalence over nontrivial rings. |
| `MonoidAlgebra.ker_augmentation_fg`, `ker_augmentation_fg_iff` | Group FG implies augmentation-kernel FG over any ring; equivalence over nontrivial rings. |
| `MonoidAlgebra.isNoetherianRing_multiplicative_int_iff`, `isNoetherianRing_iff_of_mulEquiv_int` | Infinite cyclic coefficient criterion over every ring. |
| `MonoidAlgebra.isNoetherianRing_iff_of_finiteIndex_mulEquiv_int`, `isNoetherianRing_multiplicative_int_prod_iff` | Finite-index cyclic and finite-group-product coefficient criteria, without normality. |
| `MonoidAlgebra.isNoetherianRing_of_injective`, `isNoetherianRing_subgroup` | Left-Noetherianity descends along any group-to-monoid embedding, in particular to every subgroup algebra. |
| `MonoidAlgebra.comapDomain_mapDomain`, `comapDomain_mul_mapDomain` | Coefficient retraction and right multiplication compatibility, without target cancellation. |
| `RingHom.comap_map_eq_of_additive_retraction`, `isNoetherianRing_of_additive_retraction` | Ideal extension-contraction and regular-left Noetherianity descent for an additive right retraction. |
| `RingHom.comap_map_eq_of_leftInverse` | Agreement with the ring-homomorphism retraction case of ideal extension-contraction. |
| `MonoidAlgebra.subgroup_fg_of_isNoetherianRing` | Every subgroup is FG when its group algebra over a nontrivial ring is left-Noetherian. |
| `MonoidAlgebra.augmentation_surjective` | Surjectivity over any semiring and monoid; combines with stock Noetherianity transport. |
| `MonoidAlgebra.isUnit_coeff_of_single` | A unit single term has a unit coefficient over any semiring. |
| `MonoidAlgebra.isLocalHom_of` | Basis embedding reflects units over a nontrivial semiring. |
| `MonoidAlgebra.isUnit_single_iff` | A single term is a unit iff its coefficient and index are units, over a nontrivial semiring. |
| `MonoidAlgebra.augmentation` | Coefficient-sum ring homomorphism over any semiring and monoid. |
| `MonoidAlgebra.augmentation_apply`, `MonoidAlgebra.augmentation_single` | Coefficient-sum formula and single-term simp law. |
| `MonoidAlgebra.ker_augmentation` | Kernel equals the left ideal generated by the basis differences over any ring. |
| `MonoidAlgebra.ker_augmentation_eq_span_of_submonoid_closure_eq_top`, `MonoidAlgebra.ker_augmentation_eq_span_of_subgroup_closure_eq_top` | Restrict the kernel generators to a monoid or subgroup generating set. |
| `Ideal.sub_one_mem_of_mem_submonoid_closure`, `Ideal.sub_one_mem_of_mem_subgroup_closure` | For any ring `A`, left ideal `I` and monoid homomorphism `u` into `A`, propagate `u s - 1 ∈ I` from a set to its monoid or subgroup closure. |
| `Finsupp.kerLsumEquiv` and its `_apply`, `_apply_apply`, `_symm_apply_coe`, `_symm_apply_apply`, `_symm_apply_same` laws | Off-point coordinates and extension-minus-sum inverse for the linear sum kernel. |
| `MonoidAlgebra.sumCoords_basis_apply`, `MonoidAlgebra.ker_augmentation_restrictScalars` | Semiring-level bridges from coordinate sums to augmentation. |
| `MonoidAlgebra.augmentationKerBasis`, `MonoidAlgebra.coe_augmentationKerBasis`, `MonoidAlgebra.augmentationKerBasis_repr_apply` | Coefficient-ring basis of the kernel, its vector and coordinate formulas. |
| `MvLaurentPolynomial` | Native additive-monoid-algebra Laurent model. |
| `AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial` | Equivalence from supplied free coordinates. |
| Its `_single` and `_symm_single` theorems | Forward and inverse formulas on arbitrary basis terms. |
| `FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial` | Canonical free-abelian specialization. |
| Its `_single`, `_symm_single` and `_generator` theorems | Basis and free-generator simp laws. |
| `AddChar.linearIndependent_field`, `AddChar.finite_of_field` | Field-valued independence without finiteness and finite-group character witness without roots. |
| `AddChar.natCard_eq_of_hasEnoughRootsOfUnity`, `AddChar.basisOfEnoughRootsOfUnity` and its two evaluation laws | Character cardinality and evaluation basis when enough roots exist. |
| `FiniteFourier.rightConvolution`, `FiniteFourier.rightConvolutionEigenvalue` | Algebraic matrix and positive-character eigenvalue. |
| `FiniteFourier.rightConvolution_mulVec_addChar`, `FiniteFourier.toMatrix_rightConvolution`, `FiniteFourier.rank_rightConvolution` | Eigenvectors, diagonalization and rank. |

The [Fourier guide](docs/FiniteAbelianRightConvolution.md) states exact hypotheses,
client use and limitations. The [generated Laurent API reference](docs/API.md)
is a **historical four-module/eight-Laurent snapshot**, not the current complete
library reference: it retains native displayed signatures,
implicit hypotheses, docstrings and relative source links for these eight authored
Laurent declarations. [Generation instructions](docs/README.md) explain the
snapshot's pinned tool, four-module input, source hashes and reproduction;
its previous `--check` is **not** a current whole-library check after the root
extension. A generated equation lemma for
the coordinate definition is noted separately; this documentation is not a complete
stored/private/generated-proof inventory. No dependency website or web assets ship.

For example, the following ordinary consumer uses the aggregate import only:

```lean
import GroupRings

noncomputable section

example (A : Type*) [CommSemiring A] (σ : Type*) :
    MonoidAlgebra A (Multiplicative (FreeAbelianGroup σ)) ≃ₐ[A]
      MvLaurentPolynomial σ A :=
  FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ

example (A : Type*) [CommSemiring A] (σ : Type*) (i : σ) (a : A) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ
        (MonoidAlgebra.single (.ofAdd (FreeAbelianGroup.of i)) a) =
      AddMonoidAlgebra.single (Finsupp.single i 1) a := by
  simp
```

The inverse formula sends a basis vector with exponent `m` to the group element
whose coordinates are `m`. As algebra equivalences, the constructions preserve
addition, multiplication and coefficients and satisfy both inverse laws. The
persistent [ordinary-import clients](tests/GroupRingsTest/PublicAPIClient.lean) exercise these
properties, empty/infinite indices, reducibility and degenerate coefficients.
The [generator regression clients](tests/GroupRingsTest/GeneratorSimpClient.lean) also check
generic `simp`, named `rw`, explicit `simp only`, and restricted simplification
with both general single laws disabled. Together these are 28 Laurent private
tests in the default build, not additional exported API. Six further private
checks in the [Fourier client](tests/GroupRingsTest/FiniteAbelianRightConvolutionClient.lean)
exercise the ordinary public import, positive point-mass sign and comparison
with mathlib's `AddChar.complexBasis`. The generator test with
`i : Fin 0` is vacuous; the separate empty-index equivalence still checks the
actual empty variable type.

The named generator law remains a simp rule with priority 1100, ahead of the
default-priority general single laws. Simply deleting its registration would
break the restricted-simp regression despite passing ordinary `simp` tests.
The priority change preserves the theorem's statement and proof and avoids its
observed `simpNF` redundancy finding. It does not promise compatibility with
every custom simp set or a performance improvement.

## Reproducible build and checks

Install [elan](https://github.com/leanprover/elan). The checkout pins Lean
`leanprover/lean4:v4.34.0-rc2`. The three direct library dependencies are Mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, released
[multivariate-polynomials](https://github.com/FormalFrontier/multivariate-polynomials)
at `2c9624942362c6d8de7389e77a5ca7ba7838af78`, and released
[group-theory](https://github.com/FormalFrontier/group-theory)
at `da81dc691eabf38306f427465ea8a4af350f0aef`.
`lake-manifest.json` resolves thirteen pinned packages in total, including the
transitive Formal Frontier libraries `coherent-modules` and
`algebraic-direct-limits`.
The native module interface requires the pinned toolchain; an older Lean release
is not supported by this checkout.

From a checkout of the intended revision, first fetch the matching dependency
cache, then build both default targets, including the existing and new clients:

```sh
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true tests/GroupRingsTest/PublicAPIClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/GeneratorSimpClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/FiniteAbelianRightConvolutionClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/AugmentationClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/SingleUnitsClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/AugmentationBasisClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/AugmentationGeneratorsClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/SubgroupIdealsClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/SubgroupIdealsFGClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/NoetherianClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/AugmentationNilpotenceClient.lean
```

To check a saved copy of the example above, run `lake env lean MyClient.lean`
from the same project environment. A dependent Lake project should pin an
officially published revision and compatible dependency graph, then import
`GroupRings` normally. No private native records are needed to use the library.

## References, provenance and AI involvement

For classical integral augmentation-ideal and group-homology background, see
Kenneth S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics,
Springer, 1982, [doi:10.1007/978-1-4684-9327-6](https://doi.org/10.1007/978-1-4684-9327-6).
The [augmentation-cotangent guide](docs/AugmentationCotangent.md) explains the
arbitrary-ring generalization and its independent universal-property proof.

The scalar-restriction induction generalizes Junyan Xu's Mathlib
`IsSemiprimaryRing.induction` to uniform powers of an arbitrary ideal action.
It uses Mathlib's semilinear submodule correspondence and Andrew Yang's
composition-length formalization, including exact additivity in `ℕ∞`.
The semiprimary induction and surjective algebra-map length comparison are
recovered as specializations. The semisimplicity criterion instead takes a
complement of the common-annihilator submodule and applies the existing
common-annihilator theorem on that complement. Canonical restriction reuses
Mathlib's quotient action on set-torsion modules and bijective semilinear
semisimplicity transport; its Jacobson radical supplies the weaker criterion.

Module-map detection reuses Mathlib's linear restriction, ideal multiplication
of submodules, and `Submodule.mapQ` on the original quotients. Its general
nilpotent-ideal arguments use the common-annihilator theorem and the cokernel,
without a finite-generation version of Nakayama. For modular group-ring
background, see D. S. Passman, *The Algebraic Structure of Group Rings*, Wiley,
1977.

The implementation reuses mathlib's `AddMonoidAlgebra.toMultiplicativeAlgEquiv`,
`AddMonoidAlgebra.domCongr` and `FreeAbelianGroup.equivFinsupp`; it does not copy or
replace their implementations. Their upstream authors and license notices remain
in the pinned dependency. Augmentation reuses mathlib's `mapDomainRingHom`
and `uniqueRingEquiv`; the kernel basis reuses its linear Finsupp restriction,
extension and sum API, `MonoidAlgebra.coeffLinearEquiv`, `MonoidAlgebra.basis`,
`Basis.sumCoords`, submodule equivalences and `Basis.ofRepr`.
Group-subalgebra Noetherianity uses its unchanged-coefficient pushforward,
additive coefficient pullback and Finsupp retraction, coefficient multiplication
laws, ideal span induction and well-founded-order characterization of left
Noetherianity. The left-ideal proof uses its coefficient expansion,
additive-homomorphism sum laws and ideal-closure API. Generating-set results
reuse this kernel theorem and mathlib's left module quotients, stabilizers and
closure order laws; the generic difference-membership lemmas require neither
a two-sided ideal nor a group structure on the target ring. Single-term unit
reflection uses this augmentation and mathlib's coefficient-vanishing laws to
extract both one-sided index inverses, then its commuting-factor unit and
product-unit APIs for the criterion. A motivating mathematical
reference for Laurent coordinates is Charles A.
Weibel, *The K-book: An Introduction to Algebraic K-theory*, complete-book build
August 29, 2013, Example I.2.1.2. Only the algebra-identification premise motivates
this unit, not its following projective-freeness conclusion. No source PDF or
source proof excerpt is distributed here.

AI agents contributed the code, proofs, clients, documentation and metadata.
[Credits](CREDITS.md) identify Prism's Laurent expression, Anchor's documentation
adapter, Beacon's character experiment and design advice, other Formal Frontier
AI contributions, Lattice's mathematical review and the upstream work followed.
These credits distinguish actual Lean expression origins from bibliographic
sources; they assert neither source coverage nor a redistribution right to
Weibel's book. No private project artifact is needed to import and use `GroupRings`.
