# Usage and API inventory

Start with the [root overview](../README.md), or consult the
[complete headline catalogue](HeadlineResults.md) for detailed hypotheses.
This guide collects the dependency setup, module and declaration tables,
aggregate-import example, client commands and mathematical references.
For the cotangent, nilpotence, subgroup, quotient, fixed-vector, simple-module,
Noetherian and Fourier APIs, the catalogue also links the dedicated guides.

- [Library and release scope](#library-and-release-scope)
- [Using the library and choosing imports](#using-the-library)
- [Simple ring quotients](#simple-ring-quotients)
- [Central summands detected by characters](#central-summands-detected-by-characters)
- [Reproducible build and checks](#reproducible-build-and-checks)
- [References, provenance and AI involvement](#references-provenance-and-ai-involvement)

## Library and release scope

Monoid-algebra single-term units and augmentation-kernel bases, group algebras with
explicit free abelian coordinates, and algebraic finite-abelian character
convolution, formalized in Lean.

Authors: Formal Frontier Agents

License: [Apache-2.0](../LICENSE) for original project contributions. Dependencies
retain their own licenses and contributor notices.

This guide describes the API in this checkout. Use an exact official release
revision when pinning a dependency; [formalization.yaml](../formalization.yaml)
records scope and attribution, not a live release registry.

## Using the library

Add the dependency to your `lakefile.toml`:

```toml
[[require]]
name = "group-rings"
git = "https://github.com/FormalFrontier/group-rings.git"
rev = "main"
```

GitHub `main` contains only reviewed releases. Lake resolves a release when you
add or update the dependency; `lake-manifest.json` locks that commit until the
next update. For a specific release, replace `main` with its full commit from
that history. Libraries used together must share a compatible Lean toolchain
and the same mathlib revision.

Import `GroupRings`, or one of its leaf modules:

The representation-only normalized norm and its comparison with Mathlib's
`averageMap` are supplied by `group-theory` and re-exported by `GroupRings`.
Use their canonical `GroupTheory.*` imports; the local
`GroupRings.MonoidAlgebra.AveragingProjector` instead acts on the original given
group-algebra module. Generic Noetherian retraction descent comes from
`CoherentModules.RingTheory.Noetherian.Retraction`.

| Module | Contents |
| --- | --- |
| `GroupRings.MonoidAlgebra.Matrix` | Canonical finite-matrix / monoid-algebra ring equivalence, coefficient and single laws, and matrix-unit products. |
| `GroupRings.MonoidAlgebra.Regular` | Regular monic basis differences for cancellative monoids, additive transport and the necessary Artinian torsion condition. |
| `GroupRings.MonoidAlgebra.Artinian` | The arbitrary-ring left-Artinian group-algebra criterion, including the zero-ring alternative and direct group finiteness over nontrivial coefficients. |
| `GroupRings.LaurentPolynomial.Artinian` | Coefficient multiplication laws, regular monic Laurent differences and the arbitrary-ring Artinian criterion. |
| `GroupRings.MonoidAlgebra.SubgroupIdeals` | Left coset coefficient sums and subgroup left ideals, inclusion and normality. |
| `GroupRings.MonoidAlgebra.SubgroupIdealsFG` | Finite generation of subgroup left ideals and augmentation kernels. |
| `GroupRings.MonoidAlgebra.SubgroupBasis` | Right-coset bases, left subgroup-algebra coordinates and finite-index module finiteness over semirings. |
| `GroupRings.MonoidAlgebra.Noetherian` | Left-Noetherian ascent for finitely generated commutative monoids, group-subalgebra descent, finite-index equivalence over rings and necessary conditions. |
| `GroupRings.MonoidAlgebra.CyclicNoetherian` | Direct import: cyclic coefficient criterion, group-equivalence and finite-index transport, finite-group products. |
| `GroupRings.MonoidAlgebra.MapDomain` | Coefficient projection retracts pushforward and commutes with right multiplication by a group image. |
| `GroupRings.RingTheory.Noetherian` | Deprecated compatibility import for `CoherentModules.RingTheory.Noetherian.Retraction`, the ideal extension-contraction and left-Noetherian descent API for additive right retractions. |
| `GroupRings.MonoidAlgebra.Units` | Single-term units and reflection by the basis embedding. |
| `GroupRings.MonoidAlgebra.AugmentationNilpotence` | Uniform group exponents from augmentation nilpotence over nontrivial rings of prime characteristic. |
| `GroupRings.MonoidAlgebra.AugmentationNilpotence.Finite` | Exact cardinality bound for finite p-groups over any ring with p=0, and the finite-group criterion. |
| `GroupRings.MonoidAlgebra.AugmentationNilpotence.LocallyFinite` | Elementwise nilpotence of the augmentation kernel for locally finite p-groups over any ring with p=0. |
| `GroupRings.MonoidAlgebra.AugmentationNilpotence.Converse` | Nilpotence forces zero coefficients or group finiteness; arbitrary-group prime-characteristic classification. |
| `GroupRings.RingTheory.Ideal.Annihilator` | Uniformly nilpotent actions, nonzero common vectors and two-sided-ideal annihilator submodules. |
| `GroupRings.MonoidAlgebra.FixedVectors` | Augmentation annihilation iff canonical fixedness, and nonzero fixed vectors for finite p-group modules. |
| `GroupRings.MonoidAlgebra.ModuleRepresentation` | Canonical representations and faithful intertwiner packaging on given modules over any semiring. |
| `GroupRings.MonoidAlgebra.ModuleRepresentationEquiv` | Additive Hom correspondence on original modules, inverse evaluation, lift reflection and the commutative Mathlib comparison. |
| `GroupTheory.RepresentationAveragingProjector` | Normalized representation norm over any semiring, fixed range, idempotence, naturality and self-intertwiner uniqueness. |
| `GroupTheory.RepresentationAveragingProjectorComparison` | Agreement with Mathlib's invariant-space averaging map under its commutative-ring hypotheses. |
| `GroupRings.MonoidAlgebra.AveragingProjector` | Finite-only normalized norm on given group-algebra modules, every-unit sum formula, full fixed-vector span and naturality. |
| `GroupRings.MonoidAlgebra.ModuleMaps` | Coefficient-and-basis criterion for linearity over any monoid algebra. |
| `GroupRings.MonoidAlgebra.ModuleDetection` | Canonical fixed-vector and coinvariant maps, their characteristic laws, and detection for finite p-group algebras. |
| `GroupRings.RingTheory.Ideal.ModuleDetection` | Nilpotent Nakayama and detection of injectivity and surjectivity by nilpotent ideals. |
| `GroupRings.RingTheory.Ideal.ScalarRestriction` | Uniform ideal-action induction; quotient-surjective restriction preserves both chain conditions and composition length, including infinity. |
| `GroupRings.RingTheory.Ideal.SquareQuotient` | Canonical commuting left and right quotient-ring actions on an ideal modulo its square, with Noetherian inheritance. |
| `GroupRings.MonoidAlgebra.ModuleFiniteness` | Noetherianity, Artinianity and length under canonical coefficient restriction for finite p-group algebras. |
| `GroupRings.RingTheory.Ideal.Semisimple` | Nilpotent ideal actions on semisimple modules vanish; canonical restriction and module-radical semisimplicity criteria. |
| `GroupRings.MonoidAlgebra.SemisimpleModules` | Semisimplicity for finite p-group algebras iff canonical coefficient semisimplicity and trivial group action. |
| `GroupRings.RingTheory.Ideal.Powers` | Ordered mixed products, ideal-power iteration and extension bounds over semirings. |
| `GroupRings.MonoidAlgebra.Augmentation` | Coefficient-sum augmentation and left-ideal kernel generators. |
| `GroupRings.MonoidAlgebra.CoefficientIdeals` | Ordinary left coefficient ideals, coefficient kernels and quotient equivalences. |
| `GroupRings.MonoidAlgebra.KernelPowers` | Coefficient change preserves and reflects zero kernel powers at each fixed exponent over arbitrary semirings and monoids. |
| `GroupRings.MonoidAlgebra.FiniteCoefficientIdeal` | Uniform support bounds and finiteness of a cancellative monoid from a nonzero coefficient-finite left ideal. |
| `GroupRings.MonoidAlgebra.MixedQuotient` | Simultaneous coefficient/index kernels and range or surjective quotients. |
| `GroupRings.Polynomial.CoefficientIdeals` | Constant, coefficient, ideal and kernel transport from polynomials. |
| `GroupRings.MonoidAlgebra.CoefficientChange` | Augmentation naturality, kernel preimages and ideal extension; left-Artinian descent along right-compatible additive coefficient retractions, including every homomorphism from a division ring to a nontrivial semiring. |
| `GroupRings.MonoidAlgebra.AugmentationGenerators` | Kernel generators from monoid or subgroup generating sets. |
| `GroupRings.RingTheory.Ideal.MonoidHom` | Difference-membership propagation through monoid and subgroup closure in any ring's left ideals. |
| `GroupRings.LinearAlgebra.Finsupp.SumKernel` | Pointed coefficient-sum kernel equivalence for modules over semirings. |
| `GroupRings.MonoidAlgebra.AugmentationBasis` | Left coefficient-module basis and its coordinate and vector laws. |
| `GroupRings.FreeAbelian.LaurentPolynomial` | Laurent coordinates and free-abelian specialization. |
| `GroupRings.FiniteAbelian.RightConvolution` | Character bases and Fourier convolution. |
| `GroupRings.MonoidAlgebra.ProductCoefficients` | Equality and zero detection by one chosen coefficient after all right products, or all left products, over groups and arbitrary semirings. |
| `GroupRings.MonoidAlgebra.Center` | Central coefficients, conjugation criteria and vanishing on infinite conjugacy orbits over arbitrary semirings. |
| `GroupRings.RingTheory.Artinian` | Left-Artinian descent along additive right-compatible retractions over arbitrary semirings. |
| `GroupRings.RingTheory.Artinian.FiniteCharacterBlock` | Central summands finite over the commutative base ring, detected by characters of algebras Artinian on both sides. |
| `GroupRings.RingTheory.IdempotentCentrality` | Positive-layer corner propagation and centrality modulo nilpotent two-sided ideals with both first-layer corner conditions. |
| `GroupRings.RingTheory.Module.QuotientActions` | Commuting actions descend to annihilating-ideal scalar quotients; two-sided ideals give quotient-ring modules. |
| `GroupRings.RingTheory.Module.ScalarRestriction` | Greatest scalar-finite submodules of Noetherian semimodules, endomorphism invariance, and the two-sided regular-module ideal. |
| `GroupRings.RingTheory.Congruence.Coatomic` | Compactness of the greatest ring congruence and coatomicity with only addition and `MulZeroOneClass`. |
| `GroupRings.RingTheory.SimpleRing.Quotient` | Simplicity of a congruence quotient iff its congruence is a coatom, and a nonzero simple quotient of every nontrivial unital ring. |
| `GroupRings.RingTheory.SimpleRing.Module` | A simple algebra with a nontrivial base-Noetherian module is Noetherian and finite over its commutative base ring. |
| `CoherentModules.RingTheory.Noetherian.Retraction` | Dependency-supplied ideal extension-contraction and left-Noetherian descent along additive right retractions; preferred over the compatibility import. |
| `GroupRings.RepresentationTheory.AveragingProjector` | Compatibility import of the canonical `GroupTheory.RepresentationAveragingProjector` dependency module. |
| `GroupRings.RepresentationTheory.AveragingProjectorComparison` | Compatibility import of `GroupTheory.RepresentationAveragingProjectorComparison`; no separate local construction. |

These are native Lean modules with deliberate public exports; no private import
is required by consumers.

| Declaration | Purpose |
| --- | --- |
| `RingCon.isCompactElement_top` | The greatest congruence is compact for `[Add R] [MulZeroOneClass R]`; supplies `IsCoatomic (RingCon R)`. |
| `RingCon.isSimpleRing_quotient_iff_isCoatom` | For `[NonAssocRing R]`, characterize simple canonical quotients without assuming the source or quotient nontrivial. |
| `RingCon.exists_isSimpleRing_quotient` | For `[NonAssocRing R] [Nontrivial R]`, obtain a congruence whose canonical quotient is nonzero and simple. |
| `MonoidAlgebra.moduleCoefficientModule_apply` | The canonical coefficient action is the action of `single 1 r` in the given module, over any semiring and monoid. |
| `MonoidAlgebra.moduleCoefficientModule_isScalarTower` | A locally installable scalar tower for the ordinary coefficientwise action on `R[M]` and the canonical coefficient restriction on the given module. |
| `MonoidAlgebra.cosetSum`, `cosetSum_single`, `cosetSum_apply` | Coefficient-linear coset projection, basis simp law and finite-support formula. |
| `MonoidAlgebra.mem_span_subgroup_iff` | Subgroup left-span membership iff every left-coset coefficient sum vanishes, over any ring. |
| `MonoidAlgebra.single_sub_one_mem_span_subgroup_iff`, `span_subgroup_le_iff` | Over a nontrivial ring, reflect subgroup membership and inclusion. |
| `MonoidAlgebra.span_subgroup_isTwoSided`, `span_subgroup_isTwoSided_iff` | Normality implies two-sidedness over any ring; the converse needs nontriviality. |
| `MonoidAlgebra.span_subgroup_fg_of_fg`, `span_subgroup_fg_iff` | Subgroup FG implies left-ideal FG over any ring; equivalence over nontrivial rings. |
| `MonoidAlgebra.ker_augmentation_fg`, `ker_augmentation_fg_iff` | Group FG implies augmentation-kernel FG over any ring; equivalence over nontrivial rings. |
| `MonoidAlgebra.isNoetherianRing_multiplicative_int_iff`, `isNoetherianRing_iff_of_mulEquiv_int` | Infinite cyclic coefficient criterion over every ring. |
| `MonoidAlgebra.isNoetherianRing_iff_of_finiteIndex_mulEquiv_int`, `isNoetherianRing_multiplicative_int_prod_iff` | Finite-index cyclic and finite-group-product coefficient criteria, without normality. |
| `MonoidAlgebra.isNoetherianRing_of_fg` | A finitely generated commutative monoid algebra over any left-Noetherian ring is left-Noetherian. |
| `MonoidAlgebra.isNoetherianRing_of_injective`, `isNoetherianRing_subgroup` | Left-Noetherianity descends along any group-to-monoid embedding, in particular to every subgroup algebra. |
| `MonoidAlgebra.comapDomain_mapDomain`, `comapDomain_mul_mapDomain` | Coefficient retraction and right multiplication compatibility, without target cancellation. |
| `RingHom.comap_map_eq_of_additive_retraction`, `isNoetherianRing_of_additive_retraction` | Ideal extension-contraction and regular-left Noetherianity descent for an additive right retraction. |
| `RingHom.comap_map_eq_of_leftInverse` | Agreement with the ring-homomorphism retraction case of ideal extension-contraction. |
| `MonoidAlgebra.subgroup_fg_of_isNoetherianRing` | Every subgroup is FG when its group algebra over a nontrivial ring is left-Noetherian. |
| `MonoidAlgebra.augmentation_surjective` | Surjectivity over any semiring and monoid; combines with stock Noetherianity transport. |
| `MonoidAlgebra.isUnit_coeff_of_single` | A unit single term has a unit coefficient over any semiring. |
| `MonoidAlgebra.isLocalHom_of` | Basis embedding reflects units over a nontrivial semiring. |
| `MonoidAlgebra.isUnit_single_iff` | A single term is a unit iff its coefficient and index are units, over a nontrivial semiring. |
| `MonoidAlgebra.augmentation` | Coefficient-sum ring homomorphism over any semiring and monoid. |
| `MonoidAlgebra.augmentation_apply`, `MonoidAlgebra.augmentation_single` | Coefficient-sum formula and single-term simp law. |
| `MonoidAlgebra.ker_augmentation` | Kernel equals the left ideal generated by the basis differences over any ring. |
| `MonoidAlgebra.isNilpotent_of_augmentation_eq_zero` | For locally finite p-groups over any ring with prime p=0, every augmentation-zero element is nilpotent, with an element-dependent exponent. |
| `MonoidAlgebra.ker_augmentation_eq_span_of_submonoid_closure_eq_top`, `MonoidAlgebra.ker_augmentation_eq_span_of_subgroup_closure_eq_top` | Restrict the kernel generators to a monoid or subgroup generating set. |
| `Ideal.sub_one_mem_of_mem_submonoid_closure`, `Ideal.sub_one_mem_of_mem_subgroup_closure` | For any ring `A`, left ideal `I` and monoid homomorphism `u` into `A`, propagate `u s - 1 ∈ I` from a set to its monoid or subgroup closure. |
| `Finsupp.kerLsumEquiv` and its `_apply`, `_apply_apply`, `_symm_apply_coe`, `_symm_apply_apply`, `_symm_apply_same` laws | Off-point coordinates and extension-minus-sum inverse for the linear sum kernel. |
| `MonoidAlgebra.sumCoords_basis_apply`, `MonoidAlgebra.ker_augmentation_restrictScalars` | Semiring-level bridges from coordinate sums to augmentation. |
| `MonoidAlgebra.augmentationKerBasis`, `MonoidAlgebra.coe_augmentationKerBasis`, `MonoidAlgebra.augmentationKerBasis_repr_apply` | Coefficient-ring basis of the kernel, its vector and coordinate formulas. |
| `MvLaurentPolynomial` | Native additive-monoid-algebra Laurent model. |
| `AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial` | Equivalence from supplied free coordinates. |
| Its `_single` and `_symm_single` theorems | Forward and inverse formulas on arbitrary basis terms. |
| `FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial` | Canonical free-abelian specialization. |
| Its `_single`, `_symm_single` and `_generator` theorems | Basis and free-generator simp laws. |
| `AddChar.linearIndependent_field`, `AddChar.finite_of_field` | Field-valued independence without finiteness and finite-group character witness without roots. |
| `AddChar.natCard_eq_of_hasEnoughRootsOfUnity`, `AddChar.basisOfEnoughRootsOfUnity` and its two evaluation laws | Character cardinality and evaluation basis when enough roots exist. |
| `FiniteFourier.rightConvolution`, `FiniteFourier.rightConvolutionEigenvalue` | Algebraic matrix and positive-character eigenvalue. |
| `FiniteFourier.rightConvolution_mulVec_addChar`, `FiniteFourier.toMatrix_rightConvolution`, `FiniteFourier.rank_rightConvolution` | Eigenvectors, diagonalization and rank. |

The [Fourier guide](FiniteAbelianRightConvolution.md) states exact hypotheses,
client use and limitations. The [generated Laurent API reference](API.md)
is a **historical four-module/eight-Laurent snapshot**, not the current complete
library reference: it retains native displayed signatures,
implicit hypotheses, docstrings and relative source links for these eight authored
Laurent declarations. [Generation instructions](README.md) explain the
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
persistent [ordinary-import clients](../tests/GroupRingsTest/PublicAPIClient.lean) exercise these
properties, empty/infinite indices, reducibility and degenerate coefficients.
The [generator regression clients](../tests/GroupRingsTest/GeneratorSimpClient.lean) also check
generic `simp`, named `rw`, explicit `simp only`, and restricted simplification
with both general single laws disabled. Together these are 28 Laurent private
tests in the default build, not additional exported API. Six further private
checks in the [Fourier client](../tests/GroupRingsTest/FiniteAbelianRightConvolutionClient.lean)
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

## Simple ring quotients

Import `GroupRings.RingTheory.SimpleRing.Quotient` (or `GroupRings`). For
`[NonAssocRing R] [Nontrivial R]`,
`RingCon.exists_isSimpleRing_quotient (R := R)` yields a congruence `c` and
`hc : IsSimpleRing c.Quotient`. Installing `hc` as a local instance also gives
`Nontrivial c.Quotient` by Mathlib's simplicity API. The map is the existing
`c.mk' : R →+* c.Quotient`, with surjectivity `c.mk'_surjective`; no new
quotient representation or chosen quotient construction is involved.

For a specified congruence, use `RingCon.isSimpleRing_quotient_iff_isCoatom`.
For a specified proper congruence, the generic lattice theorem
`eq_top_or_exists_le_coatom` supplies a larger coatom. These results need no
commutativity, associativity, Artinianity, Noetherianity or finiteness.
Coatomicity itself uses only `[Add R] [MulZeroOneClass R]` and remains true for
a subsingleton ring. Only the existence of a nonzero simple quotient requires
`Nontrivial R`: the top congruence, and every congruence of the zero ring, has
a trivial quotient and is not a coatom.

## Central summands detected by characters

The [central-summand theorem](HeadlineResults.md#central-summands-finite-over-the-base-ring)
uses the given central `R`-algebra structure on `A` and its inherited action
on `Ideal.span ({e} : Set A)`. It does not replace this action, assume the
whole algebra finite over `R`, or identify module finiteness with a field
dimension. Both left and right Artinianity of `A` are hypotheses; the
character is split-surjective, so Artinianity of `R` follows rather than
being an additional assumption.

The greatest finite-base left ideal in the semisimple Jacobson quotient is
two-sided and centrally idempotent-generated. Its support acts identically on
every compatible base-Noetherian representation. Applied on both sides of the
first radical layer, this makes the two support operators agree. An idempotent
lift is then central, and nilpotent ideal-action finiteness measures its left
ideal. The character is compared in `R ⧸ Ring.jacobson R`, rather than in `R`.

More explicitly, writing `J = Ring.jacobson A` and `S = A ⧸ J`, the greatest
finite-base supports for `S` and `Sᵐᵒᵖ` are compared first on the regular
bimodule, then on the ordinary first layer
`J ⧸ Submodule.comap J.subtype (J ^ 2)`. This layer keeps its original `R`
action and the commuting left and right quotient actions. Its two
Noetherian actions follow from the corresponding chain conditions on `A`
and `Aᵐᵒᵖ`. Equality of the support operators gives both first-layer corner
conditions for the centrality criterion, not merely centrality modulo `J`.

For the lifted central idempotent `e`, put `M = A e` and
`N = Module.annihilator A M`. The quotient `A ⧸ (J ⊔ N)` is a finite-base
image of the quotient principal ideal, and nilpotence of `J` implies that
some power of `J ⊔ N` annihilates `M`. The ideal-action finiteness theorem
therefore applies to `M`, not to all of `A`. Finally, the character induces
`S →ₐ[R] R ⧸ Ring.jacobson R`; its value on `e` is one in this quotient.
An idempotent congruent to one modulo the Jacobson radical is a unit and
hence equals one. These arguments include zero and nonreduced base rings
and do not require a map `S →ₐ[R] R`.

## Reproducible build and checks

Install [elan](https://github.com/leanprover/elan). The checkout pins Lean
`leanprover/lean4:v4.34.0-rc2`. The four direct library dependencies are Mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, released
[coherent-modules](https://github.com/FormalFrontier/coherent-modules)
at `c22b6cc43e81a2ef1649ac37b19e66f8ea9e107d`, released
[multivariate-polynomials](https://github.com/FormalFrontier/multivariate-polynomials)
at `616945c1c06d1655887100fe8a40e06a4a4a6d76`, and released
[group-theory](https://github.com/FormalFrontier/group-theory)
at `07948c9888686ade711654c1433c3efb2652e1aa`.
`lake-manifest.json` resolves fourteen pinned packages in total, including the
transitive Formal Frontier libraries `homological-algebra` and
`algebraic-direct-limits`.
The native module interface requires the pinned toolchain; an older Lean release
is not supported by this checkout.

From a checkout of the intended revision, first fetch the matching dependency
cache, then build both default targets, including the public-import clients:

```sh
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true tests/GroupRingsTest/PublicAPIClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/GeneratorSimpClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/FiniteAbelianRightConvolutionClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/AugmentationClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/SingleUnitsClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/AugmentationBasisClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/AugmentationGeneratorsClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/SubgroupIdealsClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/SubgroupIdealsFGClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/NoetherianClient.lean
lake env lean -DwarningAsError=true tests/GroupRingsTest/AugmentationNilpotenceClient.lean
```

To check a saved copy of the example above, run `lake env lean MyClient.lean`
from the same project environment. A dependent Lake project should pin an
officially published revision and compatible dependency graph, then import
`GroupRings` normally. No private native records are needed to use the library.

## References, provenance and AI involvement

For classical integral augmentation-ideal and group-homology background, see
Kenneth S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics,
Springer, 1982, [doi:10.1007/978-1-4684-9327-6](https://doi.org/10.1007/978-1-4684-9327-6).
The [augmentation-cotangent guide](AugmentationCotangent.md) explains the
arbitrary-ring generalization and its independent universal-property proof.

The group-algebra Artinian criterion is classical; see Passman's book cited
below. The proof here first passes to a nonzero simple two-sided coefficient
quotient and then descends to its centre field using the right-linear
coefficient retraction. Mathlib supplies the centre-field theorem and opposite
and inversion equivalences. Only at this commutative field stage is the
opposite group algebra known to be left Artinian. This library's
finite-character block theorem gives a nonzero ideal finite over the field;
its finite-support criterion gives group finiteness. Augmentation gives
coefficient necessity, and Mathlib's finite coefficient-module instance and
finite-module Artinian ascent give the converse. No finite centre degree or
right-Artinian assumption on the original coefficients is used.

The Laurent Artinian criterion follows the regular-nonunit obstruction used for
polynomial rings in `MultivariatePolynomials.Artinian` from the
[multivariate-polynomials library](https://github.com/FormalFrontier/multivariate-polynomials).
It reuses Mathlib's Laurent polynomial model and coefficient API, its generic
Artinian regular-element theorem, and `AddMonoidAlgebra.liftNCRingHom` for evaluation
at one with noncommutative coefficients. An alternative Laurent-specific
mathematical argument can use the largest exponent in a finite support. The
implemented route instead specializes the cancellative-index regularity theorem,
whose finite-support orbit argument handles both sides separately; the polynomial variable alone is not an
obstruction because it is a unit after passing to Laurent polynomials.

The scalar-restriction induction generalizes Junyan Xu's Mathlib
`IsSemiprimaryRing.induction` to uniform powers of an arbitrary ideal action.
The ideal-action finiteness criterion likewise extends Xu's
`IsSemiprimaryRing.finite_of_isNoetherian` to uniformly nilpotent actions of
arbitrary two-sided ideals. It uses Mathlib's semilinear submodule correspondence
and Andrew Yang's composition-length formalization, including exact additivity in `ℕ∞`.
The semiprimary induction and surjective algebra-map length comparison are
recovered as specializations. The semisimplicity criterion instead takes a
complement of the common-annihilator submodule and applies the existing
common-annihilator theorem on that complement. Canonical restriction reuses
Mathlib's quotient action on set-torsion modules and bijective semilinear
semisimplicity transport; its Jacobson radical supplies the weaker criterion.

Module-map detection reuses Mathlib's linear restriction, ideal multiplication
of submodules, and `Submodule.mapQ` on the original quotients. Its general
nilpotent-ideal arguments use the common-annihilator theorem and the cokernel,
without a finite-generation version of Nakayama. For modular group-ring
background, see D. S. Passman, *The Algebraic Structure of Group Rings*, Wiley,
1977.

For the center over commutative rings, compare the identity-twist specialization of
Praveen Manju and Rajendra Kumar Sharma, *(σ, τ)-Derivations of Group Rings with Applications*,
arXiv:2303.04372v3 (2024), [§4.2, Lemma 4.12](https://arxiv.org/html/2303.04372v3#S4.Thmtheorem12).
Its finite conjugacy-class-sum description concerns arbitrary groups with commutative
unital ring coefficients. The coefficient criterion and finite-support consequences here
are proved independently for arbitrary semirings, keeping coefficient centrality explicit;
no twisted-center or class-sum basis construction is claimed.

The implementation reuses mathlib's `AddMonoidAlgebra.toMultiplicativeAlgEquiv`,
`AddMonoidAlgebra.domCongr` and `FreeAbelianGroup.equivFinsupp`; it does not copy or
replace their implementations. Their upstream authors and license notices remain
in the pinned dependency. Augmentation reuses mathlib's `mapDomainRingHom`
and `uniqueRingEquiv`; the kernel basis reuses its linear Finsupp restriction,
extension and sum API, `MonoidAlgebra.coeffLinearEquiv`, `MonoidAlgebra.basis`,
`Basis.sumCoords`, submodule equivalences and `Basis.ofRepr`.
Group-subalgebra Noetherianity uses its unchanged-coefficient pushforward,
additive coefficient pullback and Finsupp retraction, coefficient multiplication
laws, ideal span induction and well-founded-order characterization of left
Noetherianity. The left-ideal proof uses its coefficient expansion,
additive-homomorphism sum laws and ideal-closure API. Generating-set results
reuse this kernel theorem and mathlib's left module quotients, stabilizers and
closure order laws; the generic difference-membership lemmas require neither
a two-sided ideal nor a group structure on the target ring. Single-term unit
reflection uses this augmentation and mathlib's coefficient-vanishing laws to
extract both one-sided index inverses, then its commuting-factor unit and
product-unit APIs for the criterion. A motivating mathematical
reference for Laurent coordinates is Charles A.
Weibel, *The K-book: An Introduction to Algebraic K-theory*, complete-book build
August 29, 2013, Example I.2.1.2. Only the algebra-identification premise motivates
this unit, not its following projective-freeness conclusion. No source PDF or
source proof excerpt is distributed here.

AI agents contributed the code, proofs, clients, documentation and metadata.
[Credits](../CREDITS.md) distinguish mathematical background, formalization and
expression lineage, original module transport and dependency contributions.
Attribution does not establish copyright ownership or permission to redistribute
third-party expression, including Weibel's book.
