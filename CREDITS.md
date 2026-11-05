# Credits

Authors: Formal Frontier Agents. AI agents contributed this library's code,
proofs, clients, documentation and metadata.

## Mathematical and formalization sources

Kenneth S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics,
Springer, 1982, [doi:10.1007/978-1-4684-9327-6](https://doi.org/10.1007/978-1-4684-9327-6),
is cited as classical integral augmentation-ideal and group-homology background.
The augmentation-cotangent result generalizes the integral comparison to any
unital coefficient ring, including noncommutative rings.
Its proof is an independent universal-property construction, not a proof adapted
from Brown or another published argument. The construction uses coefficient-linear
extension, descent through the ordinary ideal-product square, abelianization,
and the integer tensor product. It reuses Mathlib's ideal-product induction,
group abelianization and tensor-product APIs. The mathematical construction is
explained in the [augmentation-cotangent guide](docs/AugmentationCotangent.md).

Cotangent coefficient covariance uses the same universal lift with canonical
restriction of scalars. Its naturality and binary monoid-product splitting
reuse the preceding cotangent maps and delta multiplication relation.
The tensor-side map uses Mathlib's `TensorProduct.map`, additive integer-linear
maps and `Abelianization.map`; the construction does not follow a separate
published proof of these compatibility laws.

D. S. Passman, *The Algebraic Structure of Group Rings*, Wiley, 1977, is
cited as classical modular group-ring background for finite-p-group
augmentation nilpotence. The proof here is a direct central-subgroup induction
using Mathlib's group-theoretic results, extended to arbitrary coefficient rings,
not a transcription of a proof from that book.

The arbitrary-ring left-Artinian group-algebra criterion is also classical;
see Passman's book cited above. The proof here passes to a nonzero simple
two-sided coefficient quotient and then its centre field, using this library's
right-linear coefficient retraction. Group inversion over the field permits
use of this library's finite-character block theorem and finite-support
criterion. Mathlib supplies the centre-field theorem, opposite equivalences,
surjective Artinian transport and finite-module Artinian ascent. This is not
a transcription of a proof from Passman's book, and no finite degree over the
centre is assumed.
The right-cancellative monoid extension reduces to that group criterion through
the canonical units group, without changing the index operations. The local
semiring argument uses Mathlib's coefficient multiplication laws and Artinian
regular-element criterion together with this library's single-term unit
reflection. Mathlib supplies the units coercion, multiplicative equivalence
and index-induced ring equivalence. The group criterion's simple-quotient and
finite-character proof is reused without alteration.

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
additive-right-retraction criterion is provided by
[coherent-modules](https://github.com/FormalFrontier/coherent-modules) in
`CoherentModules.RingTheory.Noetherian.Retraction`. Its proof uses Mathlib's ideal
span induction and well-founded-order characterization of Noetherianity, and
agrees with Mathlib's ideal inclusion for ring-homomorphism retractions.
Coefficient-ideal membership uses Mathlib's ordinary left ideal span induction,
ordered convolution and finite coefficient reconstruction. Its polynomial
bridges use `Polynomial.toFinsuppIso` and
`AddMonoidAlgebra.toMultiplicative`, relating the result to
`Ideal.mem_map_C_iff` and `Polynomial.ker_mapRingHom`. Coefficient and mixed
quotients transport Mathlib's first-isomorphism equivalences. The mixed kernel
uses the group-to-monoid kernel theorem in this library together with Mathlib's
coefficient/index naturality and ring-to-ring ideal extension-contraction.
Augmentation nilpotence uses Mathlib's ideal-power membership and vanishing
lemmas, the prime-characteristic commuting binomial identity and the injective
monoid-algebra basis embedding. The ordered-list power API uses its additive
closure of set powers and finite-list representation of ordered set products.
The uniform exponent argument combines these interfaces directly. The finite
p-group cardinality bound uses a central-subgroup induction, with Mathlib's
nontrivial-center theorem, Cauchy's theorem, cyclic subgroup cardinality and
Lagrange's theorem. Its quotient kernel uses the canonical subgroup-relation
kernel and difference propagation from subgroup generators. The power
calculation reuses Mathlib's singleton-span powers, characteristic binomial
identity, ordinary ideal extension and ideal-power laws; no commutative-ring
model replaces the group ring.
The canonical representation on a given monoid-algebra module uses Mathlib's
`Representation.ofDistribMulAction`, introduced in its monoid representation
development by Antoine Labelle. Its original-module intertwiner packaging uses
Mathlib's `Representation.IntertwiningMap` by Stepan Nesterov and Edison Xie.
The commutative comparison uses Mathlib's existing `ofModule` and `ofModule'`
constructions and the scalar-restriction additive equivalence. The triviality
corollary reuses this library's finite-p-group semisimplicity theorem.
The additive Hom correspondence generalizes Mathlib's
`Representation.IntertwiningMap.equivLinearMapAsModule`, with its commutative
specialization compared through `Representation.asModuleEquiv`. Its inverse on
given modules uses this library's coefficient-and-basis scalar compatibility
criterion rather than a second finitely supported induction.
Projectivity ascent uses the given-lift averaging theorem in
[Group Theory](https://github.com/FormalFrontier/group-theory/tree/da81dc691eabf38306f427465ea8a4af350f0aef),
which extends the averaging construction in Mathlib's Maschke formalization
from arbitrary coefficient-linear lifts. The proof combines that theorem
with the original-module Hom correspondence and Mathlib's projectivity lifting
property and free-cover characterization; it does not repeat the averaging proof.
The normalized representation norm and its comparison with Mathlib's
invariant-space averaging map are provided by
[Group Theory](https://github.com/FormalFrontier/group-theory) in
`GroupTheory.RepresentationAveragingProjector` and
`GroupTheory.RepresentationAveragingProjectorComparison`. The group-algebra
adapter transports that self-intertwiner through the original-module Hom
correspondence, preserving the carrier, coefficient action and values.
Lean and Lake provide the proof assistant and
build system; Lean, mathlib and doc-gen4 retain their authorship and license notices. Generated
Markdown contains this project's docstrings and native signatures, not copied
dependency implementation, docstrings or website assets.

## Formalization lineage

The coefficientwise fiber-normalization statements and proofs in
`GroupRings.MonoidAlgebra.FiberNormalization` are taken from the formalization
by Formal Frontier Agents in
[Toric Ideals, `ToricIdeals/MonoidAlgebra/FiberNormalization.lean`](https://github.com/FormalFrontier/toric-ideals/blob/b901b56520453dfae376345fb1d4fa001cd5b405/ToricIdeals/MonoidAlgebra/FiberNormalization.lean).
Only the enclosing `ToricIdeals` namespace has been removed; the original
Apache-2.0 license and authorship notice are preserved.

The coefficient-generic Laurent construction adapts an earlier integral
coordinate formalization: the equivalence composition, forward basis proof and
canonical/generator pattern follow that construction. Inverse basis laws,
coefficient generality and independent universes extend it. The integer generator
expression also follows an earlier adapter; restricted-simp and priority clients
are separate diagnostic work. These are Lean expression origins, not merely a
bibliographic citation or a claim to an entirely original proof.

The documentation's module inventory, native signature/source-range handling and
binding adapt the earlier Ideal Completion documentation adapter and recipe. Generic-field
Fourier formalization adapts an earlier finite-abelian character experiment;
related design advice is distinct from copied documentation implementation.
Further collective AI contributions include the character/convolution API and
applications, single-term unit and pointed sum-kernel proofs, subgroup difference
ideals and coset sums, coefficient and mixed quotients, and augmentation-nilpotence
bounds and their clients.

The ideal-action induction and finiteness argument adapt Junyan Xu's Mathlib
`IsSemiprimaryRing.induction` and `IsSemiprimaryRing.finite_of_isNoetherian` in
`Mathlib/RingTheory/HopkinsLevitzki.lean`, extending them to arbitrary uniformly
nilpotent ideal actions. The original human copyright and authorship notice is
retained in [ScalarRestriction.lean](GroupRings/RingTheory/Ideal/ScalarRestriction.lean).
Length transport reuses Andrew Yang's composition-length formalization and exact
additivity in `ℕ∞`.

## Finite type

The semiring finite-type criterion adapts Johan Commelin's finite-support
extraction and support-span argument in
[`Mathlib.RingTheory.FiniteType`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/FiniteType.lean),
following the additive criterion's support-span proof and extending the
commutative-ring monoid-algebra criteria to commutative semirings, with the
zero-coefficient alternative. Its authentic copyright and
authorship notice is retained in the
[finite-type module](GroupRings/MonoidAlgebra/FiniteType.lean). The proof reuses Mathlib's
semiring support-generation, free-algebra lifting and finite-type surjection
APIs, algebra-adjoin span formula, and monoid-label span detection; it does not
repeat their supporting constructions. Mathlib's coefficient-preserving
multiplicative type-tag equivalence supplies the additive criterion. These are
formalization and proof-approach credits; the dependencies retain their own
licenses and notices as described below.

## Relative module finiteness and monomial subalgebras

The map-domain support-span and finite-cover engine generalizes the
polynomial-support → monoid-algebra supported-span → finite-support-union
formalization approach by Formal Frontier Agents in
[Toric Ideals' monomial-subalgebra API](https://github.com/FormalFrontier/toric-ideals/blob/be9082bc88281b6b2cde171029265a6057a54aed/ToricIdeals/MonoidAlgebra/MonomialSubalgebra.lean)
and its
[finite-cover proofs](https://github.com/FormalFrontier/toric-ideals/blob/be9082bc88281b6b2cde171029265a6057a54aed/ToricIdeals/MonoidAlgebra/MonomialFinite.lean).
These predecessors already allow arbitrary exponent monoids over commutative
semirings. The given-map criterion also allows noncommutative coefficient
semirings; the monomial-subalgebra span and three generic finite-cover
statements use that same engine with their original inclusion actions.
The monomial-subalgebra definition and its characteristic support API retain
expression from these Formal Frontier modules. The scalar-action span and
finite-module proofs use the one generalized map-domain engine. This credits
expression lineage and the proof approach separately.

Mathlib supplies finite generation (Johan Commelin), monoid-algebra modules and
restricted support (Johannes Hölzl, Yury Kudryashov and Kim Morrison), support
estimates (Damiano Testa), adjoining and subalgebra lattices (Kenny Lau and
Yury Kudryashov), and scalar restriction (Nathaniel Thomas, Jeremy Avigad,
Johannes Hölzl and Mario Carneiro). Its span API is due to Johannes Hölzl,
Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis and Heather
Macbeth. Original Formal Frontier expression is Apache-2.0; authentic dependency
licenses and notices remain with their contributions. These academic credits
are separate from copyright ownership or permission to redistribute expression.

## Finite presentation

Finite presentation of commutative monoid algebras combines Mathlib's finite-type
and finite-presentation theory (Johan Commelin), monoid finite generation
(Riccardo Brasca), finite-presentation base-change stability (Christian Merten),
and monoid-algebra scalar base change (Michał Mrugała). The additive instance
uses Mathlib's coefficient-preserving multiplicative type-tag equivalence.

## Commutative-monoid and cyclic Noetherianity

The commutative-group classification and finite-index commutative-subgroup
criterion combine this library's commutative-monoid ascent, augmentation,
subgroup finite-generation necessity and finite-index equivalence. The ascent
uses `AddMonoidAlgebra.isNoetherianRing_finsupp` from
[multivariate-polynomials](https://github.com/FormalFrontier/multivariate-polynomials).
Mathlib supplies group-finiteness conversions, operation-preserving
commutativity promotions and Noetherianity of modules over the zero ring.
The cyclic criteria specialize this general API and retain their earlier
group-equivalence and finite-product constructions.

The earlier cyclic proof used the Laurent ascent from multivariate-polynomials
and Mathlib's Laurent/group-algebra ring equivalence and generic Noetherianity
transport. That ascent uses the unit-clearing ideal criterion provided by
[coherent-modules](https://github.com/FormalFrontier/coherent-modules).
This earlier formalization is part of the cyclic API's lineage; its public
Laurent import is retained. Subgroup ascent uses this library's finite-index basis.

## Finite-group crossed maps

Crossed-map principalization uses the classical finite-group averaging argument
in Brown’s book cited above. The formalization applies additive-action cocycle
averaging and additive-map naturality from
[Group Theory](https://github.com/FormalFrontier/group-theory/blob/da81dc691eabf38306f427465ea8a4af350f0aef/GroupTheory/CocycleAveraging.lean)
to the canonical coefficient restriction of the given group-algebra module.
The augmentation-ideal consequence uses this library’s full group-algebra-linear
crossed-map universal property.

## Units and unique products

Andrzej Strojnowski, *A note on u.p. groups* (1980), supplies the classical
passage from unique-product **groups** to two unique products, as credited in
Mathlib's `Algebra.Group.UniqueProds.Basic`. The multiplicative theorem
`MonoidAlgebra.isUnit_iff_exists_single_units` in
`GroupRings.MonoidAlgebra.UnitsUniqueProds` instead assumes a two-unique-product
monoid and a no-zero-divisor semiring. This broader monoid/semiring
classification and its proof are not attributed to Strojnowski's group theorem.

The proof applies this library's convolution support estimate
`MonoidAlgebra.one_lt_card_support_coeff_mul` to a unit and its inverse, then
Mathlib's `Finsupp.card_support_le_one'` theorem to obtain a single-term
presentation. It passes the original unit hypothesis to this library's
already-single criterion `MonoidAlgebra.isUnit_single_iff`, whose index
reflection uses both left and right inverse identities. Mathlib supplies
`MonoidAlgebra.coeff_single`, `MonoidAlgebra.ext`, `MonoidAlgebra.coeff_zero`
and the identity-support APIs.
When the coefficient semiring is subsingleton, the proof uses identity unit
witnesses rather than a support-cardinality-one assertion. These mathematical and formalization-approach
credits do not assert a transcription of the article or permission to
redistribute its text.

The additive-index counterpart reuses the multiplicative classification through
Mathlib's `AddMonoidAlgebra.toMultiplicative` ring equivalence and its single-term
law, generic multiplicative-equivalence unit transport, and the public type-tag
laws and index-unit constructors. Both index inverse equations are preserved;
the coefficient semiring and its multiplicative units are unchanged. No second
classification argument is introduced.

## Convolution support and unique products

The convolution support-cardinality estimate in
`GroupRings.MonoidAlgebra.SupportUniqueProds` combines Mathlib's public
two-unique-products field and uniqueness eliminator (from Damiano Testa's
unique-product development) with its convolution coefficient, Finsupp support
and finite-set cardinality APIs. It applies already to a magma of indices over
a no-zero-divisor semiring.

Andrzej Strojnowski, *A note on u.p. groups* (1980), supplies the classical
group ingredient underlying Mathlib's passage from unique products to two
unique products. The magma/semiring support estimate is not attributed to
that group theorem or a transcription of the article's proof. This mathematical
and formalization credit does not imply permission to redistribute the article.

## Augmentation projectivity

The necessity theorem for the canonical augmentation semimodule combines
Mathlib's generic projective lifting property, its monoid-algebra
single-product coefficient formula, Finsupp support and finite-sum APIs, and
its commuting-product unit criterion. The action is scalar restriction along
this library's coefficient-sum augmentation. These formalization-approach
credits are separate from the dependency licenses and notices retained below.

## License and rights

Original project contributions and identified project adaptations use
[Apache-2.0](LICENSE). Dependencies retain their own licenses and notices.
Contributor credit and bibliographic citation do not establish copyright
ownership or grant permission to redistribute third-party expression.
Bibliographic references do not imply source-author endorsement.
