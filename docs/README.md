# API reference generation

[API.md](API.md) is generated Markdown for the eight authored public declarations defined
by group-rings: native displayed signatures with implicit parameters, source
docstrings and relative links to this same checkout. The root README supplies
the mathematical overview and ordinary-import example. Private tests and
generated helpers still require a separate complete proof audit.

No dependency website, JavaScript, fonts, styles or remote assets are shipped.
This reference does not offer interactive search or document all of Lean/mathlib.
Displayed headers may use short names in their source namespace; they are not
standalone proof-bearing Lean commands.

## Reproduction

Use Python 3 and unchanged native doc-gen4 at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, with its committed five-dependency
manifest and Lean `v4.34.0-rc2`, in a separate checkout. Build the core-only tool
with `lake build doc-gen4`. If needed, add the directory containing `elan which
lean` to the build process's PATH to expose the runtime compiler wrapper. Do not
change either project's manifest or mathematical pins to install the tool.

Fetch group-rings' matching mathlib cache before building its four modules.
Run the native executable in this project's `lake env`, not the tool's, and
analyze every module below into one fresh database. The test lean_lib uses
`srcDir = "tests"`, so its file paths differ from its module names.

| Module | Source path |
| --- | --- |
| `GroupRings.FreeAbelian.LaurentPolynomial` | `GroupRings/FreeAbelian/LaurentPolynomial.lean` |
| `GroupRings` | `GroupRings.lean` |
| `PublicAPIClient` | `tests/PublicAPIClient.lean` |
| `GeneratorSimpClient` | `tests/GeneratorSimpClient.lean` |

For example, replace executable/output paths and `FULL_SOURCE_COMMIT` with the
full source revision used for the native analysis. To reproduce the retained
reference, use `analyzed_source_revision` from `api-manifest.json`; its seven
source/pin inputs must match this checkout exactly. That historical object need
not exist in a source-only or independent parentless checkout:

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

By default, generation and `--check` first validate the **existing** manifest's
exact source/pin hashes, native-record hashes, analyzed revision, tool and module/
public inventories. They never read Git history or silently adopt changed inputs.
Generation reproduces outputs and records the current adapter hash; `--check`
compares the entire generated reference and manifest without writing. Thus an
adapter change requires explicit regeneration and fresh review, not an ignored
hash difference. Retained native records are still needed to replay this check;
they are evidence rather than bundled dependency documentation.

For an intentionally new native analysis, including first generation, use
`--refresh-binding` instead of `--check`. This authoring mode requires the chosen
full source commit to be available locally and checks every source/pin blob
against it before writing a new binding. Supply freshly generated native records
for that same revision; preserve the actual run, exact graph and source/artifact
evidence and obtain independent review. The flag is not a way to accept stale
records or a certification of their origin. It cannot be combined with `--check`.
Ordinary reproduction of an existing binding never needs that authoring flag.

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
hash. Later documentation-only commits may retain it when those inputs remain
identical. Any source/pin change requires fresh native generation and an explicit
new binding. A mutable manifest is not self-authenticating: jointly forged inputs
and hashes are outside this comparison's guarantee. Independent evidence binds
the final full candidate commit/tree, actual native run and reviewed file bytes;
the manifest does not attempt to contain its own future commit ID. `--check`
compares bytes against retained inputs; it does not authenticate their origin,
prove remote source-URL availability, approve a public history or recheck proofs.

## Provenance

Authors: Formal Frontier Agents. Original project contributions are Apache-2.0.
Prism (AI agent) adapted Anchor's (AI agent) generator, tests and recipe from
ideal-completion at `f0c8c34386109116e4912fb425a8ad15d9dc42a4`, modifying the
inventory, test paths, signatures, assumptions and binding. That input was
unreviewed; neither its tests nor status approve this adaptation.
Prism subsequently added the retained-input/explicit-refresh split and parentless
controls after reproducing the old recipe's internal-Git-object dependency.
Beacon supplied related portability design advice, not copied implementation.

Generated Markdown contains this project's docstrings and native displayed
mathematical signatures, not copied dependency implementations or docstrings.
No doc-gen4 web assets are shipped. Lean, mathlib and doc-gen4 retain their credit
and licenses upstream. Exact generated artifacts, adapted tooling, notices and
proposed public history still require independent rights review.
