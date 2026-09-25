#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
# Original adapter: Anchor (AI), ideal-completion f0c8c34386109116e4912fb425a8ad15d9dc42a4.
# Modified by Prism (AI): group-rings inventory, paths, assumptions and portable binding.
"""Generate this library's Markdown API from pinned native doc-gen4 records.

This is a deliberately eight-declaration adapter, not a general documentation
certifier, a Lean parser, or a proof check. Native generation receipts remain
separate review evidence. See docs/README.md for the reproduction contract.
"""
import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess

TOOL = "97d4ecdfc8e09e7f511724c25e303d448de6a3db"
MODULE_PATHS = {
    "GroupRings.FreeAbelian.LaurentPolynomial": "GroupRings/FreeAbelian/LaurentPolynomial.lean",
    "GroupRings": "GroupRings.lean",
    "PublicAPIClient": "tests/PublicAPIClient.lean",
    "GeneratorSimpClient": "tests/GeneratorSimpClient.lean",
}
MODULES = tuple(MODULE_PATHS)
INPUTS = tuple(MODULE_PATHS.values()) + (
    "lean-toolchain", "lakefile.toml", "lake-manifest.json")
EXPECTED = {
    "MvLaurentPolynomial": "def",
    "AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial": "def",
    "AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial_single": "theorem",
    "AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial_symm_single": "theorem",
    "FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial": "def",
    "FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_single": "theorem",
    "FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_symm_single": "theorem",
    "FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_generator": "theorem",
}


def assumptions(name):
    if name == "MvLaurentPolynomial":
        return ("σ : Type u", "A : Type v", "Semiring A")
    if name.startswith("AddEquiv."):
        return ("A : Type u", "G : Type v", "σ : Type w",
                "CommSemiring A", "AddCommGroup G")
    return ("A : Type u", "σ : Type v", "CommSemiring A")


def displayed_kind(name, kind):
    if name == "MvLaurentPolynomial":
        return "abbrev"
    return "noncomputable def" if kind == "def" else kind


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def load_json(path):
    return json.loads(path.read_bytes(), object_pairs_hook=unique_object)


def native_hashes(records):
    return {m: digest(json.dumps(records[m], sort_keys=True).encode()) for m in MODULES}


def validate_binding(binding, revision, sources, records):
    """Check retained inputs, not the truth or independent approval of their origin."""
    require(type(revision) is str and re.fullmatch(r"[0-9a-f]{40}", revision) is not None,
            "full source revision required")
    require(type(binding) is dict and set(binding) == {
        "format", "generator", "docgen_revision", "adapter_sha256",
        "analyzed_source_revision", "modules", "inputs", "public_declarations",
        "native_record_sha256", "api_sha256", "proof_certification"},
        "binding fields differ")
    require(type(binding["format"]) is int and binding["format"] == 1,
            "binding format differs")
    require(binding["generator"] == "scripts/generate_api.py" and
            binding["docgen_revision"] == TOOL, "binding generator/tool differs")
    require(binding["analyzed_source_revision"] == revision, "binding revision differs")
    require(binding["modules"] == list(MODULES), "binding module inventory differs")
    require(type(binding["public_declarations"]) is list and
            len(binding["public_declarations"]) == len(EXPECTED) and
            all(type(name) is str for name in binding["public_declarations"]) and
            set(binding["public_declarations"]) == set(EXPECTED),
            "binding public inventory differs")
    require(set(sources) == set(INPUTS) and set(records) == set(MODULES),
            "source/native inventory differs")
    require(binding["inputs"] == {p: digest(sources[p]) for p in sorted(sources)},
            "source/pin drift from retained binding")
    require(binding["native_record_sha256"] == native_hashes(records),
            "native records drift from retained binding")
    require(binding["proof_certification"] is False, "binding claims proof certification")
    for name in ["adapter_sha256", "api_sha256"]:
        require(type(binding[name]) is str and re.fullmatch(r"[0-9a-f]{64}", binding[name]) is not None,
                "malformed binding digest: " + name)
    # A changed adapter may reproduce the same retained inputs. The regenerated
    # manifest binds the new adapter; --check compares that entire output exactly.


class Header(HTMLParser):
    """Keep all visible text, including every implicit argument; discard markup."""

    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.text = []
        self.kinds = []
        self.names = []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected native header tag")
        attrs = dict(attrs)
        require(not any(k.startswith("on") for k in attrs), "active header attribute")
        if tag == "div" and "decl_type" in attrs.get("class", "").split():
            self.text.append(" ")
        self.stack.append((tag, set(attrs.get("class", "").split())))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError("unexpected header comment")

    def handle_decl(self, _):
        raise ValueError("unexpected header declaration")

    def rendered(self):
        # Whitespace alone is normalized; all tokens and implicit binders remain.
        return " ".join("".join(self.text).split())


def render(records, revision, sources):
    require(re.fullmatch(r"[0-9a-f]{40}", revision) is not None, "full source revision required")
    require(set(records) == set(MODULES), "shipped module records differ")
    require(set(sources) == set(INPUTS), "source/pin inventory differs")
    rows = []
    found = {}
    for module in MODULES:
        record = records[module]
        require(record["name"] == module, "native module name differs")
        for row in record["declarations"]:
            info = row["info"]
            name, kind = info["name"], info["kind"]
            require(module == MODULES[0], "unexpected public declaration in re-export/examples")
            require(name in EXPECTED and EXPECTED[name] == kind, "unexpected public name/kind")
            require(name not in found, "duplicate public declaration")
            path = MODULE_PATHS[module]
            prefix = "https://github.com/FormalFrontier/group-rings/blob/" + revision + "/" + path
            link = re.fullmatch(re.escape(prefix) + r"#L([0-9]+)-L([0-9]+)", info["sourceLink"])
            require(link is not None, "native record is not bound to selected immutable source")
            require(info["docLink"] == "./" + module.replace(".", "/") + ".html#" + name,
                    "native self link differs")
            require(type(info["line"]) is int and 0 < info["line"] <= len(sources[path].splitlines()),
                    "invalid native source line")
            require(int(link[1]) == info["line"] and
                    info["line"] <= int(link[2]) <= len(sources[path].splitlines()),
                    "native source range differs")
            header = Header(row["header"])
            require("".join(header.names) == name and "".join(header.kinds) == displayed_kind(name, kind),
                    "native header identity differs")
            text = header.rendered()
            require(all(token in text for token in assumptions(name)), "implicit assumptions absent")
            require("```" not in text and "```" not in info["doc"], "unsupported Markdown fence")
            require(bool(info["doc"].strip()), "public docstring absent")
            found[name] = kind
            rows.append(dict(name=name, kind=kind, header=text,
                             doc=info["doc"].strip(), path=path, line=info["line"]))
    require(found == EXPECTED, "missing public declaration")
    rows.sort(key=lambda row: row["line"])
    lines = ["# Generated API reference", "",
             "This reference covers the eight authored public declarations of group-rings.",
             "Import `GroupRings`; its leaf is `GroupRings.FreeAbelian.LaurentPolynomial`.",
             "`PublicAPIClient` and `GeneratorSimpClient` contain private checked clients, not public API.", "",
             "The compiled environment also exposes the generated equation lemma",
             "`AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial.eq_1` for the",
             "coordinate definition. Native doc-gen4 does not list it as an authored declaration.",
             "This page is not a private/generated-declaration census or proof audit.", "",
             "Headers below are native doc-gen4 display signatures, not complete declarations",
             "with proof bodies. Short names use the source's `AddEquiv` or `FreeAbelianGroup`",
             "namespace, `open Multiplicative` and imports. Implicit parameters are displayed;",
             "`u`, `v` and `w` are universes. Source links target this same checkout.", "",
             "The source/pin hashes and generation provenance are in [api-manifest.json](api-manifest.json).",
             "See [generation instructions](README.md) and the [mathematical overview](../README.md).", ""]
    for row in rows:
        lines += ["## " + row["name"], "", "```lean", row["header"], "```", "",
                  row["doc"], "", f"[Source](../{row['path']}#L{row['line']}) (line {row['line']}).", ""]
    markdown = "\n".join(lines).encode()
    manifest = dict(format=1, generator="scripts/generate_api.py", docgen_revision=TOOL,
                    adapter_sha256=digest(Path(__file__).read_bytes()),
                    analyzed_source_revision=revision, modules=list(MODULES),
                    inputs={p: digest(sources[p]) for p in sorted(sources)},
                    public_declarations=[r["name"] for r in rows],
                    native_record_sha256=native_hashes(records),
                    api_sha256=digest(markdown), proof_certification=False)
    return markdown, (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--native-data", type=Path, required=True,
                   help="native fromDb output doc-data directory")
    p.add_argument("--source-revision", required=True)
    mode = p.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="compare retained outputs, never write")
    mode.add_argument("--refresh-binding", action="store_true",
                      help="author a new native snapshot; requires the selected Git source object")
    args = p.parse_args()
    require(re.fullmatch(r"[0-9a-f]{40}", args.source_revision) is not None,
            "full source revision required")
    root = Path(__file__).resolve().parent.parent
    sources = {path: (root / path).read_bytes() for path in INPUTS}
    records = {m: load_json(args.native_data / ("declaration-data-" + m + ".bmp"))
               for m in MODULES}
    if args.refresh_binding:
        # Explicit authoring mode for a genuinely new native run. Object equality
        # alone does not authenticate those records or approve their provenance.
        for path, raw in sources.items():
            old = subprocess.check_output(["git", "show", args.source_revision + ":" + path], cwd=root)
            require(old == raw, "source/pin drift from analyzed revision: " + path)
    else:
        # Portable reproduction must never silently absorb source/pin/record drift.
        # Exact commit/tree and native-run authentication stay in independent evidence.
        validate_binding(load_json(root / "docs/api-manifest.json"), args.source_revision,
                         sources, records)
    api, manifest = render(records, args.source_revision, sources)
    for name, raw in [("API.md", api), ("api-manifest.json", manifest)]:
        target = root / "docs" / name
        if args.check:
            require(target.read_bytes() == raw, "generated file differs: " + name)
        else:
            target.write_bytes(raw)
    print(json.dumps(dict(status="matched" if args.check else "generated",
                          declarations=len(EXPECTED), api_sha256=digest(api),
                          release_acceptance=False)))


if __name__ == "__main__":
    main()
