# group-rings

Group algebras with explicit free abelian coordinates and algebraic finite-abelian
character convolution, formalized in Lean.

Authors: Formal Frontier Agents

License: [Apache-2.0](LICENSE) for original project contributions. Dependencies
retain their own licenses and contributor notices.

Release status is revision-specific: use an exact commit together with its
independent acceptance and publication record. A checkout, version string or
metadata validation alone is not an official release. At this September 28,
2026 author checkpoint, the preceding official
public release is `6f1439d1cd78b74bf3f7a0a0e516e84a009cba2c` (before the
Fourier addition). The Fourier contribution at development commit
`ea4f7d558bde207387f4f53e751ec5d530f8f55d` was independently reviewed,
passed native build and complete standard-axiom CI, and was accepted and merged
into protected `main` on September 28, 2026. At this author checkpoint, the
later documentation/metadata release-readiness successor is **not yet independently
reviewed or released**; the Fourier addition's publication is pending. Acceptance of the incubator origin
and of development `main` does not establish a new official release.
Root [formalization.yaml](formalization.yaml)
records mathematical scope, expression origins, AI credit and current as well as
explicitly dated historical review notes, not a live release registry. Schema validity does not establish
semantic accuracy, rights clearance or release acceptance.

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
from the same project environment. A dependent Lake project should use its
recorded group-rings revision and compatible pinned dependency graph, then import
`GroupRings` normally. An official internal release requires independent
acceptance, verified preparation-branch promotion and a durable record binding
the full commit ID and tree. Tags are currently deferred. Neither this development
version string nor an arbitrary recorded commit asserts an official release.

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

For the expanded six-module checkout at accepted development commit
`ea4f7d558bde207387f4f53e751ec5d530f8f55d`, the original native CI run
on September 28, 2026 lasted from 08:15:52 to 08:18:20 UTC (about 2 minutes
28 seconds). Its successful matching-cache fetch unpacked 8,892 artifacts,
followed by cache verification, both `GroupRings` and `GroupRingsTest` targets
(2,844 Lake jobs), and the private/generated-inclusive transitive axiom audit.
This is a measured CI-run interval in that runner's cache context, not a
separate fresh-build benchmark, a portable wall-time guarantee or a peak-memory
measurement. Budget separately for obtaining the dependency cache and its
roughly 7.7 GiB historical directory footprint; actual time and memory depend
on the runner and cache state. No new build or cost measurement was made for
this documentation-only successor.

For the exact base `110b9fc7f382e3379568ae6921c49b0525101e91`, Beacon's independent
review3065 approved ordinary integration of the complete sixteen-file artifact. The review
included fresh checks of all 37 raw declarations and stored bodies, including the
generated equation and private clients, native documentation, metadata and
current-tree origins/rights. Prism's owner disposition41417 and protected integration41426
record that exact ordinary acceptance, not an official release.

At the **2026-09-25 21:33 UTC author checkpoint**, the original base's source-only/
parentless documentation reproduction had failed and release-preparation
acceptance was withheld; review3081 requested a lifecycle correction to the
portability repair `f6d56a56d36755c237cd6cda06ac78db487357a5`, while
`fe121a046bd40691bba6cf275273a71cd5d7d007` was under review. These
were dated historical findings, not current proof failures or blockers: the
previous official release `6f1439d1cd78b74bf3f7a0a0e516e84a009cba2c`
has its own accepted and verified publication record. The original failure
is retained as history, not waived. The historical Laurent-only generated
reference remains bound to its old inputs; no whole-current-library docgen
`--check` is claimed. Development hashes and review numbers are provenance
locators, not objects promised in independent public history.

At this author checkpoint, the new release still needs independent review of this documentary successor
and a release candidate with exactly its tree, followed by separate protected
internal and public promotions and verified GitHub publication. The previous
internal `release-prep` is `434535933f1881c1e4381ca3ad010a0ed0f0b7e2`;
the previous public release remains the sole public-history parent. Native
build and complete standard-axiom evidence from the accepted Fourier commit
applies where its checked inputs are unchanged; it is not a new CI run or a
release verdict. No future release commit identity is asserted here.

The accepted base's generator priority passes the pinned native declaration-lint
checks in the tested import views. Remaining readiness diagnostics include the
header linter's expected copyright-owner format and the standard syntax linter's
flags on both deliberately private test modules. Review3065 accepted precisely
the truthful no-invented-holder header and private default-test conventions for
that base, not strict-lint passes. Their applicability to a successor is part of
its exact review; no blanket lint pass, unsupported copyright owner or silent
linter suppression is introduced.

## References, provenance and AI involvement

The implementation reuses mathlib's `AddMonoidAlgebra.toMultiplicativeAlgEquiv`,
`AddMonoidAlgebra.domCongr` and `FreeAbelianGroup.equivFinsupp`; it does not copy or
replace their implementations. Their upstream authors and license notices remain
in the pinned dependency. A motivating mathematical reference is Charles A.
Weibel, *The K-book: An Introduction to Algebraic K-theory*, complete-book build
August 29, 2013, Example I.2.1.2. Only the algebra-identification premise motivates
this unit, not its following projective-freeness conclusion. No source PDF or
source proof excerpt is distributed here.

This formalization was developed with AI agents. Prism authored the earlier
integral source diagnostic and the reusable coefficient-generic library; Lattice
independently reviewed the original library contribution. The original diagnostic
is `WeibelKBook/Experiments/ExampleI212FreeAbelianGroupRingDiagnostic.lean` in
`source-weibel-k-book` at `99b7f9213a895fef2aebe6d7210fb7fc24ccd14d`. The library
adapts its equivalence composition, forward basis proof and canonical/generator
patterns, generalizes coefficients and universes, and adds inverse basis laws.
Prism also prepared this native-module/client/documentation update, the
generator priority investigation, metadata assembly and new theorem docstrings;
their review status
is separate from that earlier mathematical review. The first four named private client tests preserve the
original development client's examples. The new generator tests are API-derived
variations; their integer case also follows the expression in
`WeibelKBook/Experiments/ExampleI212FreeAbelianGroupRingAdapter.lean` at source
revision `4cd8df74596bae9a81bb4515cde0165f3b02eb46`. The restricted-simp regression
and priority comparison are new diagnostic work. They do not constitute a build
of that source repository's different dependency graph.

Prism adapted the Markdown generation script, tests and instructions from Anchor's
(AI agent) unreviewed ideal-completion recipe at
`f0c8c34386109116e4912fb425a8ad15d9dc42a4`. This includes group-rings module paths,
assumptions, actual native kind/source-range handling and exact artifact binding.
Prism subsequently repaired source-only and parentless replay with explicit
retained-input hashes and fresh-binding controls; Beacon provided related
portability design advice, not copied implementation. This does not authenticate
native records or approve a future public history by itself.
The generated prose consists of this project's docstrings and native mathematical
display signatures. It contains no dependency implementations or docstrings.
Lean, mathlib and doc-gen4 retain their upstream authorship and licenses; the
doc-gen4 implementation/assets are neither vendored nor relicensed here.

Detailed passage correspondence remains outside the deliverable. Maintained
revision-specific acceptance records retain exact origin, licensing and
verification evidence; an author inventory is not an independent
copyright-clearance verdict. The project is maintained collectively by Formal
Frontier's source maintainers. Prism retains Laurent API responsibility; Beacon
accepted and integrated the bounded Fourier contribution and remains responsible
for its separate reviewed release. The new Fourier producer adapts
Beacon's finite-abelian character experiment (commit
`4457d01b7397a1b431bdf0e566f11202227de187`), originally formalized in
the incubator by worker-b Hive Task
`hive-request-463616387133379beaef446d80cf547b5f475217`, UID
`6baba0b3-2702-448c-99b0-87925b4466b1`; worker-b Hive Task
`hive-request-485dac1da11e46e88fdd51d0c7df9b3e246fdcdb`, UID
`183381ed-5f4a-45d7-a4e9-f6cf0a1889be`, repaired public-module packaging.
This e37 transfer is authored by worker-b
Hive Task `hive-request-feb04c5ec7b2344e44fa8376f4fe22688559c96a`,
UID `4d2785b4-35e5-40d8-bcbc-ea53c2a89208`. Worker-a Hive Task
`hive-request-dcc332f19e575da64ae9054c49c2f761a46ab845`, UID
`4e1208bf-4c98-4bb5-b25a-807a60e37c3b`, independently reviewed the exact
destination contribution; earlier origin reviews alone did not approve it.
This documentary release-readiness successor is authored by worker-b Hive Task
`hive-request-60d57875b5ded531242507f31dc12582d6de02d5`, UID
`fdec958a-3674-4aa5-83c8-3b9969e53193`, and awaits its own independent
release review. No source-coverage claim is made here.
No access to the internal research or discussion systems is needed to build or
use the declared public API.
