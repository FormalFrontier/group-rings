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
basis results. The augmentation map uses mathlib's monoid-index ring
homomorphism and singleton-monoid ring equivalence. Its kernel proof uses the
monoid-algebra coefficient reconstruction, finitely supported sum laws and
left-ideal closure supplied by mathlib. Generating-set formulas reuse this
kernel theorem and mathlib's left module quotient, stabilizer submonoid and
subgroup, pullback action and closure order laws. The coefficient-module kernel basis
uses mathlib's linear Finsupp restriction, extension and sum interfaces,
monoid-algebra coefficient equivalence and basis, basis coordinate sums,
submodule equivalences and representation-based basis constructor. The generic
pointed sum-kernel equivalence combines those Finsupp primitives with an
extension-minus-sum correction. The single-term unit criterion reuses
the augmentation for coefficient reflection and mathlib's coefficient-vanishing
laws to extract left and right index inverses. Its commuting-factor and product
unit criteria, local-homomorphism interface and basis multiplication laws supply
the remaining unit API and clients. The subgroup-ideal proofs use mathlib's
coefficient-linear reindexing, left coset equality, quotient representatives,
finite coefficient reconstruction and ordinary ideal spans. These mathlib interfaces
retain their upstream authorship and license notices. Subgroup-ideal finite
generation uses mathlib's finite-subset-of-span, finite-span and group-finiteness
interfaces, combined with the subgroup-difference closure and inclusion-reflection
results. The left-Noetherian necessary conditions combine this finite-generation
criterion with mathlib's finite generation of every ideal of a left-Noetherian
ring and its generic Noetherianity transport along surjective ring homomorphisms.
Group-subalgebra descent uses mathlib's coefficient pullback, unchanged-coefficient
pushforward, Finsupp retraction and single-term multiplication laws. The generic
additive-right-retraction criterion uses its ideal span induction and
well-founded-order characterization of Noetherianity, and agrees with its
ideal inclusion for ring-homomorphism retractions.
Lean and Lake provide the proof assistant and
build system; Lean, mathlib and doc-gen4 retain their authorship and license notices. Generated
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
  and convolution mathematics, reusable library API, Fourier applications
  and mathematical review.
- **Cornice (AI agent)** supplied the single-term unit reflection proofs, the
  local basis-embedding instance, the coefficient/index unit criterion, its
  public-import clients and documentation, as well as the pointed Finsupp
  sum-kernel equivalence, its coefficient-module augmentation-kernel basis
  specialization, characteristic laws and matrix-ring client. Cornice also
  supplied the arbitrary-ring left-ideal difference-membership interfaces,
  their augmentation generating-set applications and the free-monoid and
  infinite-cyclic public-import clients. The subgroup coset-sum API, its
  characteristic left-span theorem, membership/order/normality reflection and
  nonnormal matrix-ring client are also Cornice contributions. Cornice supplied
  the subgroup-ideal and augmentation-kernel finite-generation equivalences,
  their all-ring forward implications and matrix/zero-ring public-import clients.
  Cornice also supplied augmentation surjectivity and the subgroup finite-generation
  consequence of left-Noetherianity, with the stock coefficient-descent client.
  The additive-right-retraction ideal and Noetherianity criterion, coefficient
  projection compatibility and arbitrary-semiring group-subalgebra descent are
  also Cornice contributions.
- **Lattice** supplied independent mathematical review of the Laurent contribution.

## License and rights

Original project contributions and identified project adaptations use
[Apache-2.0](LICENSE). Dependencies retain their own licenses and notices.
Contributor credit and bibliographic citation do not establish copyright
ownership or grant permission to redistribute third-party expression. No human
mathematical review, source-author endorsement or source-coverage claim is made.
