# group-rings

Group algebras with explicit free abelian coordinates, formalized in Lean.

Authors: Formal Frontier Agents

License: [Apache-2.0](LICENSE) for original project contributions. Dependencies
retain their own licenses and contributor notices.

Release status is revision-specific: use an exact commit together with its
independent acceptance and publication record. A checkout, version string or
metadata validation alone is not an official release. The ordinary-development base
`110b9fc7f382e3379568ae6921c49b0525101e91` was independently reviewed and integrated,
including the native interface, clients, metadata and generated API reference.
That acceptance does not cover the later portability repair or this lifecycle
and public-documentation update. Root [formalization.yaml](formalization.yaml)
records mathematical scope, expression origins, AI credit and a dated author-time
review snapshot, not a live release registry. Schema validity does not establish
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

## Public API and use

Import `GroupRings`. The leaf module is
`GroupRings.FreeAbelian.LaurentPolynomial`. Both are native Lean modules with
deliberate public exports; no private import is required by consumers.

| Declaration | Purpose |
| --- | --- |
| `MvLaurentPolynomial` | Native additive-monoid-algebra Laurent model. |
| `AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial` | Equivalence from supplied free coordinates. |
| Its `_single` and `_symm_single` theorems | Forward and inverse formulas on arbitrary basis terms. |
| `FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial` | Canonical free-abelian specialization. |
| Its `_single`, `_symm_single` and `_generator` theorems | Basis and free-generator simp laws. |

The [generated API reference](docs/API.md) retains native displayed signatures,
implicit hypotheses, docstrings and relative source links for these eight authored
declarations. [Generation instructions](docs/README.md) explain the pinned tool,
four-module input, source hashes and reproduction. A generated equation lemma for
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
with both general single laws disabled. Together these are 28 private tests in
the default build, not additional exported API. The generator test with
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
cache, then build all four shipped Lean modules, including the default tests:

```sh
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true tests/PublicAPIClient.lean
lake env lean -DwarningAsError=true tests/GeneratorSimpClient.lean
```

To check a saved copy of the example above, run `lake env lean MyClient.lean`
from the same project environment. A dependent Lake project should use its
recorded group-rings revision and compatible pinned dependency graph, then import
`GroupRings` normally. An official internal release requires independent
acceptance, verified preparation-branch promotion and a durable record binding
the full commit ID and tree. Tags are currently deferred. Neither this development
version string nor an arbitrary recorded commit asserts an official release.

Four-module baseline, measured on x86-64 Linux with
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

For the exact base `110b9fc7f382e3379568ae6921c49b0525101e91`, Beacon's independent
review3065 approved ordinary integration of the complete sixteen-file artifact. The review
included fresh checks of all 37 raw declarations and stored bodies, including the
generated equation and private clients, native documentation, metadata and
current-tree origins/rights. Prism's owner disposition41417 and protected integration41426
record that exact ordinary acceptance, not an official release.

The base's source-only/parentless documentation reproduction failed; complete
release-preparation acceptance was explicitly withheld. The separately proposed
repair at `f6d56a56d36755c237cd6cda06ac78db487357a5`
separates retained-input reproduction from explicit fresh binding; see
[the recipe](docs/README.md). At the **2026-09-25 21:33 UTC author checkpoint**,
Beacon's review3081 had passed its technical portability/API checks but requested
a lifecycle correction. The correction at
`fe121a046bd40691bba6cf275273a71cd5d7d007` was under separate review; this later
two-file public-documentation update had not been independently accepted.
These are historical observations, not predictions of subsequent verdicts.
Exact successor acceptance must assess unchanged proof/native evidence,
final documentation/metadata and rights. The original failure is retained,
not waived or represented as a proof failure. Neither a
selected-name axiom check, successful build nor internally consistent manifest
establishes those remaining decisions.

Publication requires an exact independently accepted internal
snapshot, guarded native reviewed fast-forward preparation, and final checks and
review of the GitHub-URL/public-lineage artifact. First-public-root replacement
and the private GitHub mirror use their separately verified operator-owned path.
Only a revision-specific acceptance/publication record establishes that those
steps occurred. The development commit identifiers and review numbers above are
provenance locators; their objects and internal records are not promised to be
available in an independently rooted release history.

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
Frontier's source maintainers, with Prism responsible for this release work.
No access to the internal research or discussion systems is needed to build or
use the declared public API.
