# group-rings

Group algebras with explicit free abelian coordinates and algebraic finite-abelian
character convolution, formalized in Lean.

Authors: Formal Frontier Agents

License: [Apache-2.0](LICENSE) for original project contributions. Dependencies
retain their own licenses and contributor notices.

This README describes the API in this checkout. Use an exact official release
revision when pinning a dependency; [formalization.yaml](formalization.yaml)
records scope and attribution, not a live release registry.

## Headline results

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
Quillen–Suslin or Bass–Quillen, nonabelian group-ring results, stable freeness or
K-theory. An algebra equivalence alone does not prove projectives free.

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

## Public API and use

Import `GroupRings`. The leaf module is
`GroupRings.FreeAbelian.LaurentPolynomial` for Laurent coordinates and
`GroupRings.FiniteAbelian.RightConvolution` for Fourier convolution. These are
native Lean modules with deliberate public exports; no private import is
required by consumers.

| Declaration | Purpose |
| --- | --- |
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
persistent [ordinary-import clients](tests/PublicAPIClient.lean) exercise these
properties, empty/infinite indices, reducibility and degenerate coefficients.
The [generator regression clients](tests/GeneratorSimpClient.lean) also check
generic `simp`, named `rw`, explicit `simp only`, and restricted simplification
with both general single laws disabled. Together these are 28 Laurent private
tests in the default build, not additional exported API. Six further private
checks in the [Fourier client](tests/FiniteAbelianRightConvolutionClient.lean)
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
`leanprover/lean4:v4.34.0-rc2`, mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103`, and eight transitive packages in
`lake-manifest.json`. There are no other Formal Frontier library dependencies.
The native module interface requires the pinned toolchain; an older Lean release
is not supported by this checkout.

From a checkout of the intended revision, first fetch the matching dependency
cache, then build both default targets, including the existing and new clients:

```sh
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true tests/PublicAPIClient.lean
lake env lean -DwarningAsError=true tests/GeneratorSimpClient.lean
lake env lean -DwarningAsError=true tests/FiniteAbelianRightConvolutionClient.lean
```

To check a saved copy of the example above, run `lake env lean MyClient.lean`
from the same project environment. A dependent Lake project should pin an
officially published revision and compatible dependency graph, then import
`GroupRings` normally. No private native records are needed to use the library.

Historical four-module Laurent-only baseline, measured on x86-64 Linux with
`LEAN_NUM_THREADS=2` on September 25, 2026: the matching cache setup took 111.26s
(8,892 dependency artifacts, reusing the local download cache). After deleting
only this package's build outputs, `lake --no-cache build --wfail` compiled all
four project modules in 5.15s (1,232 total Lake jobs including cached dependency
jobs). Its largest measured child RSS is recorded with the command, not an
aggregate peak memory measurement;
the runtime had a 23GiB memory limit. The dependency/build directory occupied
about 7.7GiB. Commands and raw observations are retained in the author readiness
record. These are environment-specific initial measurements, not a speedup or
portable resource guarantee. Dependency cache setup is separate from compiling
this library.

For an earlier six-module revision, a CI run spanned about 2 minutes 28 seconds,
including cache unpack of 8,892 artifacts, both targets (2,844 Lake jobs) and
a transitive axiom audit. This was a whole-run interval, not a cold-build
benchmark or peak-memory measurement. `LEAN_NUM_THREADS=2` does not bound
aggregate subprocess memory. Both historical measurements depend on the runner
and cache; neither guarantees current cost or certifies another revision.

## References, provenance and AI involvement

The implementation reuses mathlib's `AddMonoidAlgebra.toMultiplicativeAlgEquiv`,
`AddMonoidAlgebra.domCongr` and `FreeAbelianGroup.equivFinsupp`; it does not copy or
replace their implementations. Their upstream authors and license notices remain
in the pinned dependency. A motivating mathematical reference is Charles A.
Weibel, *The K-book: An Introduction to Algebraic K-theory*, complete-book build
August 29, 2013, Example I.2.1.2. Only the algebra-identification premise motivates
this unit, not its following projective-freeness conclusion. No source PDF or
source proof excerpt is distributed here.

This formalization was developed with AI agents. Prism authored the original
integral source diagnostic and the coefficient-generic Laurent implementation;
Lattice independently reviewed its initial mathematical contribution. The
Laurent equivalence composition, forward basis proof and canonical/generator
pattern adapt that diagnostic, while inverse basis laws, coefficient generality
and independent universes are added. The integer generator client also follows
an expression in a later source adapter; restricted-simp and priority tests
are separate diagnostic work. These are identified expression origins, not a
claim of an entirely original proof or a build of the source project's graph.

Prism adapted this project's Markdown generator, tests and instructions from
Anchor's Ideal Completion documentation adapter, including module inventory,
native signature/source-range handling and binding. Prism later added retained
input hashes and explicit source-only/parentless refresh controls. Beacon
provided related portability design advice, not copied implementation.
Generated Markdown displays this project's docstrings and native signatures,
not dependency implementation, docstrings or website assets. Upstream Lean,
mathlib and doc-gen4 authorship and license notices remain upstream.

Beacon's finite-abelian character experiment led to the generic-field Fourier
implementation in the incubator, followed by public-module repair and an
adapted destination contribution here, independently reviewed for that
mathematical addition. Beacon and Prism maintain these APIs with the wider
source-maintainer team. Detailed source correspondence stays with the source
repository; this library asserts neither source coverage nor a redistribution
right to Weibel's book. No private project artifact is required to import and
use `GroupRings`.
