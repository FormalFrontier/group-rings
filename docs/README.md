# API reference and historical binding

[API.md](API.md) is a **retained historical Laurent-slice snapshot** for eight
authored public declarations, not a current whole-library reference. It has
native displayed signatures with implicit parameters, source
docstrings and relative links to this same checkout. The root README supplies
the mathematical overview; the Fourier API is documented in the
[handwritten finite-abelian guide](FiniteAbelianRightConvolution.md), which
documents the same-checkout Fourier API. The snapshot's historical
four-module native records do not claim to inventory the current six-module
library or certify its proofs. Ordinary users can import and build `GroupRings`
without native documentation records or any other private artifacts.

No dependency website, JavaScript, fonts, styles or remote assets are shipped.
This reference does not offer interactive search or document all of Lean/mathlib.
Displayed headers may use short names in their source namespace; they are not
standalone proof-bearing Lean commands.

## Historical snapshot replay (optional)

Replaying the historical binding requires its **exact old** source/pin files
and all four native records, which are not bundled with this repository.
The historical analyzed source commit and hashes appear in
[api-manifest.json](api-manifest.json); this is not a setup step for using
the current library. For a genuine historical replay, use Python 3 and
unchanged native doc-gen4 at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, with its committed five-dependency
manifest and Lean `v4.34.0-rc2`, in a separate checkout. Build the core-only tool
with `lake build doc-gen4`. If needed, add the directory containing `elan which
lean` to the build process's PATH to expose the runtime compiler wrapper. Do not
change either project's manifest or mathematical pins to install the tool.

Fetch the matching mathlib cache before any build. The four modules
below identify the **old analysis inputs**, not the complete expanded root:
`GroupRings` now publicly imports the Fourier module and the default test
target now includes a third client. The source snapshot and native-record
binding remain historical; the Markdown preamble and adapter digest can be
updated as a separately reviewed presentation-only transformation of those
retained signatures. Neither that transformation nor the old `--check` passes
as current whole-library native generation. Do not silently refresh the
historical binding or represent an old snapshot check as acceptance of the
new API.
Run the native executable in this project's `lake env`, not the tool's, and
analyze every module below into one fresh database. The test lean_lib uses
`srcDir = "tests"`, so its file paths differ from its module names.

| Module | Source path |
| --- | --- |
| `GroupRings.FreeAbelian.LaurentPolynomial` | `GroupRings/FreeAbelian/LaurentPolynomial.lean` |
| `GroupRings` | `GroupRings.lean` |
| `PublicAPIClient` | `tests/PublicAPIClient.lean` |
| `GeneratorSimpClient` | `tests/GeneratorSimpClient.lean` |

The commands below document the **historical Laurent-only snapshot**, not
an instruction to run `--check` on this expanded checkout. They apply only
after checking out the exact `analyzed_source_revision` from the manifest,
obtaining its seven matching source/pin inputs and authentic original native
records. That Git object and the records need not be available to an ordinary
consumer or in a source-only/independent parentless checkout:

```sh
mkdir /tmp/group-docs
lake env /path/to/doc-gen4 single --build /tmp/group-docs GroupRings.FreeAbelian.LaurentPolynomial api.db https://github.com/FormalFrontier/group-rings/blob/FULL_SOURCE_COMMIT/GroupRings/FreeAbelian/LaurentPolynomial.lean
```

Repeat for the aggregate and both tests, using their exact file paths. Render
the analyzed native records, then generate and compare the reference:

```sh
mkdir /tmp/group-render
lake env /path/to/doc-gen4 bibPrepass --build /tmp/group-render --none
lake env /path/to/doc-gen4 fromDb --build /tmp/group-render --manifest /tmp/group-render/manifest.json /tmp/group-docs/api.db
python3 -B scripts/generate_api.py --native-data /tmp/group-render/doc-data --source-revision FULL_SOURCE_COMMIT
python3 -B scripts/generate_api.py --native-data /tmp/group-render/doc-data --source-revision FULL_SOURCE_COMMIT --check
python3 -B scripts/test_generate_api.py
```

At the original revision, generation and `--check` first validate the **existing** manifest's
exact source/pin hashes, native-record hashes, analyzed revision, tool and module/
public inventories. They never read Git history or silently adopt changed inputs.
Generation reproduces outputs and records the selected adapter hash; `--check`
compares the entire generated reference and manifest without writing. A
presentation-only update to this page and its literal renderer preamble can be
reviewed against the preserved eight sections and old binding without claiming
fresh native records or a passing `--check` on today's inputs. Retained native
records are still needed for genuine historical replay; they are evidence,
not bundled dependency documentation.

For an intentionally **new** native analysis, `--refresh-binding` is authoring:
it requires an actual new source Git object, matching source/pin blobs and
freshly generated native records for that same revision, with independent
review. It is not a drift fix for the old snapshot and cannot certify the
origin of records by itself. It cannot be combined with `--check`.

Retain both exact dependency graphs, effective search path and native receipts.
Generator warnings are findings, not silent passes. Intermediate HTML and its
dependency links/assets are not the distributed bundle: select only Markdown
and the binding manifest. An unpublished immutable source URL demonstrates
binding, not remote availability. Distributed links use this checkout's files.

The adapter requires all four native module records and exactly the eight public
names/kinds. It refuses missing/duplicate/unexpected entries, source/pin or revision
drift, missing docstrings, malformed headers and absent coefficient/group/index
assumptions. It retains every header text token, normalizing whitespace only.
Input JSON is not self-authenticating: native-run and output review are separate.
This is not a general API census, kernel checker or release certifier.
The loaded environment also exposes the coordinate definition's generated
`AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial.eq_1` lemma;
native documentation omits this generated entry. It remains part of the separate
proof-audit scope, together with private clients and any other generated content.

`api-manifest.json` binds the analyzed commit, four source hashes, toolchain/Lake
configuration/manifest hashes, adapter hash, native-record hashes and reference
hash. At the bound revision, documentation-only commits can retain their
historical native records. The present root/test extension leaves those records
and their source binding historical; the two output/adapter hashes reflect
only a presentation update, whose acceptance is revision-specific. A new
whole-library binding requires fresh native generation and an explicit binding.
A mutable manifest is not self-authenticating: jointly forged inputs
and hashes are outside this comparison's guarantee. Independent evidence binds
the final full candidate commit/tree, actual native run and reviewed file bytes;
the manifest does not attempt to contain its own future commit ID. `--check`
compares bytes against retained inputs; it does not authenticate their origin,
prove remote source-URL availability, approve a public history or recheck proofs.

## Provenance

Authors: Formal Frontier Agents. Original project contributions are Apache-2.0.
Prism (AI agent) adapted Anchor's (AI agent) Ideal Completion generator, tests
and recipe, modifying the module inventory, test paths, native signatures,
assumptions and binding. The donor's tests and status do not approve this
adaptation.
Prism subsequently added the retained-input/explicit-refresh split and parentless
controls after reproducing the old recipe's internal-Git-object dependency.
Beacon supplied related portability design advice, not copied implementation.

Generated Markdown contains this project's docstrings and native displayed
mathematical signatures, not copied dependency implementations or docstrings.
No doc-gen4 web assets are shipped. Lean, mathlib and doc-gen4 retain their credit
and licenses upstream. Provenance and rights for an exact published version
are subject to that version's independent review and release record; the
historical binding alone does not establish acceptance of new native inputs.
