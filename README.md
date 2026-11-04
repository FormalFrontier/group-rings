# group-rings

Group rings and monoid algebras in Lean: augmentation ideals and their modules,
subgroup and coefficient quotients, chain conditions, explicit Laurent
coordinates, and algebraic character convolution. The API allows
noncommutative and zero coefficients where the stated hypotheses permit them.

Authors: Formal Frontier Agents

## Headline results

The families below summarize the library. The
[complete catalogue](docs/HeadlineResults.md) retains the detailed statements,
qualifiers and source links; the [usage guide](docs/Usage.md) provides the
module and declaration inventories.

- **Single terms and augmentation.** Over a nontrivial semiring and any monoid,
  `IsUnit (single m r) ↔ IsUnit r ∧ IsUnit m`; coefficient-unit reflection
  also allows the zero semiring. Over any semiring and an index type with
  only multiplication, a single term is left-regular iff its coefficient is
  left-regular and either the coefficients are subsingleton or its index is
  left-regular; the [right-hand criterion](GroupRings/MonoidAlgebra/Regular.lean)
  is analogous. Augmentation is the coefficient-sum ring
  homomorphism over any semiring. Over a ring its kernel is the **left** span
  of `single m 1 - 1`, with monoid or subgroup generating-set refinements.
  `MonoidAlgebra.augmentationKerBasis` is a basis over the coefficient ring
  `R`, **not** over `R[M]`, indexed by nonidentity monoid elements.
  [Statements and modules](docs/HeadlineResults.md#single-terms-and-augmentation).

- **Coefficient tests, centers and finite matrices.** Over any possibly zero
  or noncommutative semiring, a group-algebra element is determined by one
  chosen coefficient after all right multiplications, and independently after
  all left multiplications. Centrality means central coefficients invariant
  under conjugation; coefficients vanish on infinite conjugacy orbits.
  For any monoid, finite decidable matrix indices give the ring equivalence
  `MonoidAlgebra (Matrix n n R) M ≃+* Matrix n n (R[M])`, preserving both
  multiplication orders, including empty indices.
  [Precise statements](docs/HeadlineResults.md#coefficient-tests-and-finite-matrices).

- **Crossed maps and averaging.** Over any ring and monoid, linear maps from
  the full augmentation ideal to a given left `R[M]`-module correspond
  additively to normalized crossed maps
  `z(mn) = z(m) + single m 1 • z(n)` for its canonical action.
  For a finite group of unit order in the coefficient ring, every crossed map
  is principal, with negative inverse-order sum witness, natural for additive
  maps. See the [universal property](GroupRings/MonoidAlgebra/AugmentationCrossedUniversal.lean)
  and [averaging](GroupRings/MonoidAlgebra/AugmentationAveraging.lean).

- **Augmentation cotangents.** For any unital ring and monoid, coefficient-linear
  maps from `I/I²` to a left `R`-module `V` correspond **as a set** to
  `M →* Multiplicative V`. For a group,
  `I/I² ≃ₗ[R] R ⊗[ℤ] Additive (Abelianization G)`, where `I` is the augmentation
  ideal and `I²` its ordinary ideal square. Coefficient covariance is semilinear; monoid products split by projections
  and sums of inclusions. No commutativity or freeness is required.
  [Statements](docs/HeadlineResults.md#augmentation-cotangents) ·
  [cotangent guide](docs/AugmentationCotangent.md).

- **Finite `p`-groups and fixed vectors.** For prime `p`, any ring with
  `(p : R) = 0` and finite `p`-group `G`, the augmentation ideal has zero
  `Nat.card G`-th power. Every nontrivial unital `R[G]`-module has a nonzero
  canonical fixed vector; simplicity is equivalent to simplicity under
  canonical coefficient restriction, and simple modules have trivial group
  action. For any group over any ring, augmentation nilpotence forces
  `Subsingleton R ∨ Finite G`, without a characteristic assumption. If
  `(p : R) = 0`, nilpotence is equivalent to
  `Subsingleton R ∨ (Finite G ∧ IsPGroup p G)`; over nontrivial `R` it also
  forces one common `p`-power exponent. For locally finite `p`-groups over
  any ring with `(p : R) = 0`, every augmentation-zero element is nilpotent,
  with an element-dependent exponent; no uniform kernel power is asserted.
  Under these same locally finite hypotheses, the Jacobson radical is the
  augmentation preimage of the coefficient radical. In particular, a single
  term is radical exactly when its coefficient is, and a zero coefficient
  radical gives the augmentation kernel. See the
  [radical guide](docs/Jacobson.md) and
  [statements and guides](docs/HeadlineResults.md#finite-p-groups-and-fixed-vectors).

- **Given modules and scalar restriction.** Over any semiring and monoid,
  canonical representations and an additive Hom/intertwiner correspondence
  retain the given carriers and coefficient actions. For finite groups of
  unit order in the coefficient semiring, coefficient projectivity implies
  group-algebra projectivity. The normalized norm is natural for `R[G]`-linear
  maps and is the unique `R[G]`-linear retraction onto the fixed vectors' span.
  For rings `S`, `A`, a map `φ : S →+* A` surjective modulo a
  two-sided ideal `I`, and an `A`-module `V` with
  `∃ n, I^n ≤ Module.annihilator A V`, the exact restriction
  `Module.compHom V φ` preserves and reflects both chain conditions and
  preserves length in `ℕ∞`, including infinity. Semisimplicity is equivalent
  to **annihilation by `I` and semisimplicity of that restriction**.
  For finite `p`-groups over rings with prime `p = 0`, this gives the canonical
  coefficient comparisons: semisimplicity requires coefficient semisimplicity
  **and** trivial group action. Fixed vectors detect injectivity of module
  maps; coinvariants detect surjectivity, without finite generation.
  [Statements and modules](docs/HeadlineResults.md#given-modules-and-scalar-restriction).

- **Finiteness of modules.** For rings `S`, `A`, compatible scalar towers,
  and a two-sided ideal `I`, a Noetherian `A`-module with uniformly nilpotent
  `I`-action is finite over `S` whenever `A ⧸ I` is finite over `S`; no
  surjective scalar map or nilpotence of `I` itself is needed. Separately,
  a simple algebra over a commutative ring admitting a nontrivial compatible
  module Noetherian over that base is itself Noetherian, hence finite, over
  the base; the base ring need not be Noetherian.
  A Noetherian `A`-semimodule also has a greatest `A`-submodule
  finite over compatible scalars `S`, preserved by every `A`-linear
  endomorphism. For the regular module this is a two-sided ideal. Both
  scalar semirings may be noncommutative, and `S` need not be Noetherian.
  [Greatest finite submodules](GroupRings/RingTheory/Module/ScalarRestriction.lean) ·
  [other statements and hypotheses](docs/HeadlineResults.md#given-modules-and-scalar-restriction).

- **Subgroup ideals and coset bases.** Over any ring, a subgroup's left
  difference ideal consists of elements whose coefficient sums vanish on
  **left cosets** `gH`. Over nontrivial rings these ideals reflect subgroup
  membership, inclusion, finite generation and normality via two-sidedness.
  Separately, over any semiring, `R[G]` has a **left** `R[H]`-basis indexed by
  **right cosets** `H * g`; finite index gives module finiteness.
  No normality is required for these coset constructions.
  [Statements](docs/HeadlineResults.md#subgroup-ideals-and-coset-bases) ·
  [subgroup guide](docs/SubgroupIdeals.md).

- **Coefficient and index quotients.** Over semirings, extension of any left
  coefficient ideal is characterized coefficientwise. For any semiring
  homomorphism and monoid, coefficient change preserves and reflects zero
  kernel powers at each fixed exponent, including zero, without surjectivity.
  For `Ring R`,
  `Semiring S`, `Group G`, `Monoid M`, and maps `f : R →+* S`, `φ : G →* M`,
  the mixed kernel is the sum of the extended coefficient kernel and the
  kernel-subgroup difference ideal. For arbitrary maps the quotient is the
  composite's range subsemiring; surjective `f` gives `S[MonoidHom.mrange φ]`, and
  surjectivity of both gives `S[M]`. Normal-subgroup quotients and unchanged
  coefficient kernel/range quotients have full basis and factorization laws.
  [Statements and guides](docs/HeadlineResults.md#coefficient-and-index-quotients).

- **Commuting scalar actions and central idempotents.** Commuting ring
  actions on a module remain commuting after quotienting both rings by
  annihilating ideals; two-sidedness is needed for quotient rings, not just
  their scalar actions. For any ring `A` and two-sided ideal `I`, the
  [first ideal-square quotient](GroupRings/RingTheory/Ideal/SquareQuotient.lean)
  `I/I²` has commuting left and right `A ⧸ I`-actions. In any ring, an idempotent
  central modulo a nilpotent two-sided ideal `I` is central if **both**
  off-diagonal corner maps send `I` into `I²`; quotient centrality alone is
  insufficient.
  [Actions](docs/HeadlineResults.md#given-modules-and-scalar-restriction) ·
  [centrality criterion](docs/HeadlineResults.md#chain-conditions-and-regularity).

- **Central summands detected by characters.** For a commutative ring `R`
  and an `R`-algebra `A` Artinian on both sides, every `χ : A →ₐ[R] R`
  is one on a central idempotent whose principal left ideal is finite over
  `R` with its inherited action. Zero and nonreduced base rings are allowed;
  the whole algebra need not be finite over `R`.
  [Statement and proof strategy](docs/HeadlineResults.md#central-summands-finite-over-the-base-ring).

- **Uniform binomial kernels.** For any monoid homomorphism and any ring,
  its monoid-algebra kernel is the left span of equal-image unit-basis
  differences. If the source is finitely generated and commutative, one finite
  family of index pairs works over **every** coefficient ring. Neither the
  target monoid nor the coefficients need commute; no coefficient-Noetherian
  hypothesis is needed.
  [Statements and modules](docs/HeadlineResults.md#uniform-binomial-kernels).

- **Finite type.** For any commutative semiring `R` and any monoid `M`,
  `Algebra.FiniteType R (MonoidAlgebra R M)` is equivalent to
  `Monoid.FG M ∨ Subsingleton R`. Nontrivial coefficients give simply finite
  generation of `M`; neither commutativity nor cancellation of `M` is needed.
  The additive-monoid counterpart uses the same criterion.
  [Module](GroupRings/MonoidAlgebra/FiniteType.lean) ·
  [statements and use](docs/HeadlineResults.md#finite-type).

- **Finite presentation.** For any commutative ring `R` and finitely generated
  commutative monoid `M`, the canonical `R`-algebra `R[M]` is finitely presented.
  The additive-monoid version is also an instance. Coefficients need not be
  Noetherian, and exponents need not be cancellative or finite.
  [Module](GroupRings/MonoidAlgebra/FinitePresentation.lean) ·
  [statements and use](docs/HeadlineResults.md#finite-presentation).

- **Chain conditions and regularity.** For any ring `R` and finitely generated
  **commutative** monoid `M`, `R[M]` is left-Noetherian iff `R` is.
  For a commutative group `G`, the exact criterion is left-Noetherianity of `R`
  and `Subsingleton R ∨ Group.FG G`. A finite-index finitely generated
  commutative subgroup gives the coefficient-ring criterion even when the
  ambient group is noncommutative and the subgroup is not normal. For a
  cancellative monoid over any semiring, a **nonzero** left ideal finite over
  the coefficients forces the monoid to be finite. Additive right-compatible
  coefficient retractions give left-Artinian descent without multiplicativity.
  Such a retraction exists for every homomorphism from a division ring to a
  nontrivial semiring, without centrality or finite-dimensionality assumptions.
  Left-Noetherianity descends to embedded group algebras over any semiring;
  finite-index subgroup algebras over rings share it with the whole algebra.
  Over nontrivial rings it forces every subgroup to be finitely generated,
  without a general converse. The infinite cyclic and finite-index cyclic
  criteria reduce to the coefficient ring; import
  `GroupRings.MonoidAlgebra.CyclicNoetherian` directly for these.
  Over any ring, infinite-order elements of cancellative monoids give regular
  monic basis differences, forcing torsion in left-Artinian monoid algebras
  with nontrivial coefficients. For any ring `R` and either a left-cancellative
  or a right-cancellative monoid `G`,
  [`MonoidAlgebra.isArtinianRing_iff_of_isLeftCancelMul` and
  `MonoidAlgebra.isArtinianRing_iff`](GroupRings/MonoidAlgebra/Artinian.lean)
  give that `R[G]` is left-Artinian iff `R` is left-Artinian and
  `Subsingleton R ∨ Finite G`. The corresponding `finite_of_isArtinianRing`
  theorems give monoid finiteness directly over any nontrivial ring,
  specializing to the classical group criterion.
  Locally, over a nontrivial **semiring** and any monoid, left Artinianity
  makes every right-regular index a unit; over a nontrivial **ring**, it also
  makes every left-regular index a unit, without global cancellation.
  The global criteria require **ring** coefficients. All these conditions
  use the original left regular action.
  The zero ring is allowed in the criterion, the
  universes are independent, and no commutativity or right-Artinian hypothesis
  is imposed.
  Separately, `LaurentPolynomial R` is left-Artinian iff `R` is subsingleton,
  even for noncommutative or zero rings.
  [Statements and modules](docs/HeadlineResults.md#chain-conditions-and-regularity).

- **Laurent coordinates.** Supplied coordinates `G ≃+ (σ →₀ ℤ)` identify an
  additive commutative group's algebra over a commutative semiring with
  `MvLaurentPolynomial σ A`. Free abelian groups have canonical coordinates,
  with arbitrary, empty or infinite variable types.
  [Statements and module](docs/HeadlineResults.md#laurent-coordinates).

- **Characters and right convolution.** Character evaluations on an additive
  commutative group `G` are linearly independent over any field `K`, even for
  infinite groups without enough roots. For finite `G`, enough roots of unity
  of exponent `Monoid.exponent (Multiplicative G)` give a character basis;
  with `[Fintype G]` they give diagonalization and rank for right convolution,
  whose entry is `f (-sigma + tau)` and eigenvalue is `∑ x, f x * psi x` with
  **positive** sign. The eigenvector law needs no enough-roots assumption.
  [Statements](docs/HeadlineResults.md#characters-and-right-convolution) ·
  [Fourier guide](docs/FiniteAbelianRightConvolution.md).

## Using the library

Add the public dependency to your `lakefile.toml`:

```toml
[[require]]
name = "group-rings"
git = "https://github.com/FormalFrontier/group-rings.git"
rev = "main"
```

GitHub `main` contains only reviewed releases. Lake resolves a release when
first adding or updating the dependency; `lake-manifest.json` keeps that commit
until the next update. For an explicit release pin, replace `main` with the full
commit of a release from that history. Libraries used together must share a
compatible Lean toolchain and the same Mathlib revision.

Import `GroupRings` for the aggregate API, or choose a leaf from the
[module inventory](docs/Usage.md#using-the-library). Cyclic Noetherianity needs
its direct import as noted above. No private import or documentation artifact
is needed by consumers.

The generic [ring-congruence API](docs/Usage.md#simple-ring-quotients) is also
re-exported: congruences are coatomic even over the zero ring, and a unital
ring's congruence quotient is simple exactly at a coatom. Every nontrivial
unital ring therefore has a nonzero simple quotient, using the canonical
quotient and map; multiplication need not be associative or commutative.

The aggregate import provides the canonical free-abelian equivalence:

```lean
import GroupRings

noncomputable section

example (A : Type*) [CommSemiring A] (σ : Type*) :
    MonoidAlgebra A (Multiplicative (FreeAbelianGroup σ)) ≃ₐ[A]
      MvLaurentPolynomial σ A :=
  FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ
```

See the [usage guide](docs/Usage.md) for basis and inverse formulas,
public-import clients, and the historical signature snapshot's scope.

## Reproducible build and checks

Install [elan](https://github.com/leanprover/elan). The checkout pins its
Lean toolchain in [lean-toolchain](lean-toolchain) and dependency graph in
[lake-manifest.json](lake-manifest.json); use those matching versions.
From the intended checkout revision:

```sh
lake exe cache get
lake build --wfail
```

The default targets are `GroupRings` and `GroupRingsTest`. To check a saved
copy of the example in that environment, use `lake env lean MyClient.lean`.
The [full build guide](docs/Usage.md#reproducible-build-and-checks) retains exact
versions, dependency references and individual client commands.

## Conventions and limitations

`R[M]` means `MonoidAlgebra R M`; ideals and regular module chain conditions
are left-sided. Canonical coefficient restriction is along `singleOneRingHom`,
not an unrelated action on a replacement carrier. Coefficient, index and module
universes are independent in the general APIs; semiring, ring, commutative-semiring
and field hypotheses are result-specific, as are nontriviality assumptions.
Nilpotence of an ideal **action** need not mean the ideal is nilpotent.

Single-term unit results do not classify arbitrary sums. Laurent coordinates
do not prove projective freeness or K-theory, and Fourier results do not assert
a group-algebra/convolution equivalence or a nonabelian character basis.
See the [full mathematical scope](docs/HeadlineResults.md#mathematical-scope).

## References

The [full references and formalization sources](docs/Usage.md#references-provenance-and-ai-involvement)
and [CREDITS.md](CREDITS.md) explain the Mathlib reuse, named upstream work,
Group Theory averaging, and Laurent ascent from multivariate-polynomials and
coherent-modules. Mathematical background includes Brown's *Cohomology of
Groups* and Passman's *The Algebraic Structure of Group Rings*. Weibel's
*K-book*, Example I.2.1.2, motivates only the Laurent algebra identification,
not projective freeness. The centre criterion is compared with Manju and
Sharma's identity-twist specialization for commutative coefficients in the
guides; the arbitrary-semiring proof here is independent.

## Credits and license

AI agents contributed the code, proofs, clients, documentation and metadata.
[CREDITS.md](CREDITS.md) explains the mathematical and formalization sources,
expression lineage and dependency contributions; attribution does not establish
ownership or permission to redistribute third-party expression.
Original project contributions are licensed under [Apache-2.0](LICENSE).
Dependencies retain their own licenses and contributor notices; no source book,
proof excerpt or dependency website assets are distributed here.
