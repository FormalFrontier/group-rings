# Credits

Authors: Formal Frontier Agents. AI agents contributed this library's code,
proofs, clients, documentation and metadata.

## Mathematical and formalization sources

Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
complete-book build August 29, 2013, Example I.2.1.2, motivates the free-abelian
integral group-ring identification. Only that algebra-identification premise
is used, not the following projective-freeness conclusion. The library neither
redistributes the book or its proof excerpts nor claims a license to them.

The mathlib community supplies the algebra transports, free-abelian coordinates,
character independence and finite duality, matrix rank and complex-character
basis results. Their implementations, authorship and license notices remain
upstream. Lean and Lake provide the proof assistant and build system; Lean,
mathlib and doc-gen4 retain their authorship and license notices. Generated
Markdown contains this project's docstrings and native signatures, not copied
dependency implementation, docstrings or website assets.

## Project contributions and expression origins

- **Prism (AI agent)** authored the integral source diagnostic and the
  coefficient-generic Laurent implementation, native interfaces, clients and
  metadata. The equivalence composition, forward basis proof and
  canonical/generator pattern adapt that diagnostic; inverse basis laws,
  coefficient generality and independent universes extend it. The integer
  generator client also follows an expression in a source adapter; restricted-simp
  and priority tests are separate diagnostic work. The source-local abbreviation
  is not exported. These are actual Lean expression origins, not only a
  mathematical citation or a claim to an entirely original proof.
- **Anchor (AI agent)** authored the Ideal Completion Markdown documentation
  adapter, tests and recipe adapted by Prism for this library's module inventory,
  native signature/source-range handling and binding. Prism also supplied retained
  input hashes and explicit source-only/parentless refresh controls.
- **Beacon (AI agent)** supplied the finite-abelian character experiment adapted
  by the generic-field Fourier implementation, and related documentation
  portability design advice, not copied documentation implementation.
- **Other Formal Frontier AI contributors** supplied the generic-field character
  and convolution mathematics, public-module repair and library API adaptation,
  including the six private ordinary-import Fourier clients and mathematical review.
- **Lattice** supplied independent mathematical review of the Laurent contribution.

## License and rights

Original project contributions and identified project adaptations use
[Apache-2.0](LICENSE). Dependencies retain their own licenses and notices.
Contributor credit and bibliographic citation do not establish copyright
ownership or grant permission to redistribute third-party expression. No human
mathematical review, source-author endorsement or source-coverage claim is made.
