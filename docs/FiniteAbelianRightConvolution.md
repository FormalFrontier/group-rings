# Finite-abelian characters and right convolution

Import `GroupRings` to use the character-basis and convolution API from
`GroupRings.FiniteAbelian.RightConvolution`. The development is algebraic:
`G : Type u` is an additive commutative group and `K : Type v` is a field, with
independent universes. No topology, complex coefficients, characteristic-zero
assumption or group-algebra identification is needed.

## Character basis

`AddChar.linearIndependent_field` proves that field-valued additive characters
are linearly independent as functions `G → K`, without assuming `G` finite or
that `K` has enough roots of unity. With `[Finite G]`, the independent witness
`AddChar.finite_of_field` supplies `Finite (AddChar G K)` without a roots
assumption.

For the full character basis, additionally assume
`[HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative G))]`.
`AddChar.natCard_eq_of_hasEnoughRootsOfUnity` equates the cardinalities of the
dual and `G`; `AddChar.basisOfEnoughRootsOfUnity` is a basis of `G → K`, and
`AddChar.coe_basisOfEnoughRootsOfUnity` and
`AddChar.basisOfEnoughRootsOfUnity_apply` identify its vectors with character
evaluations. Mathlib already supplies `AddChar.complexBasis` for complex
coefficients; the ordinary-import client compares the two bases at `K = ℂ`.

## Right convolution

With `[Fintype G]` and `[Field K]`, the matrix
`FiniteFourier.rightConvolution f` has entry
`(FiniteFourier.rightConvolution f) sigma tau = f (-sigma + tau)`.
Its eigenvalue at a character `psi` is

```lean
FiniteFourier.rightConvolutionEigenvalue f psi = ∑ x : G, f x * psi x
```

The theorem `FiniteFourier.rightConvolution_mulVec_addChar` gives
`rightConvolution f *ᵥ (psi : G → K) =
rightConvolutionEigenvalue f psi • (psi : G → K)` even without enough roots.
The sign is positive: for the point mass at `a`, the eigenvalue is `psi a`,
**not** `psi (-a)`.

When the field has enough roots of unity,
`FiniteFourier.toMatrix_rightConvolution` diagonalizes the convolution operator
in the character basis. Its public statement explicitly requires
`[Fintype (AddChar G K)] [DecidableEq (AddChar G K)]`; these may be supplied
locally, rather than installing a global character-index instance:

```lean
import GroupRings

open Multiplicative
open scoped Matrix

noncomputable section

example {G K : Type*} [AddCommGroup G] [Field K] [Fintype G]
    [HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative G))]
    (f : G → K) :
    (FiniteFourier.rightConvolution f).rank =
      Nat.card {psi : AddChar G K //
        FiniteFourier.rightConvolutionEigenvalue f psi ≠ 0} := by
  exact FiniteFourier.rank_rightConvolution f
```

To call the matrix theorem, use `classical`, then local instances:

```lean
  letI : Finite (AddChar G K) := AddChar.finite_of_field (G := G) (K := K)
  letI : Fintype (AddChar G K) := Fintype.ofFinite (AddChar G K)
  exact FiniteFourier.toMatrix_rightConvolution f
```

The rank formula needs **no** character-index `Fintype` in its public statement:
it counts the characters whose positive-character eigenvalue is nonzero using
`Nat.card`. Full diagonalization requires the commutativity of `G` and enough
roots in `K`; it does not establish a nonabelian Fourier basis or a formal
group-algebra/convolution equivalence. The Laurent-coordinate API is separate
and its weaker semiring and possibly infinite-index assumptions remain intact.

## Reproduction and provenance

The checkout pins Lean `v4.34.0-rc2`, mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103` and its resolved Lake
manifest. From the repository root, install the pinned toolchain, then run
`lake exe cache get` **before** `lake build --wfail`; the `GroupRingsTest`
target includes six private ordinary-import Fourier client checks in
`tests/FiniteAbelianRightConvolutionClient.lean`, alongside the existing
Laurent clients. The original native CI run on accepted development commit
`ea4f7d558bde207387f4f53e751ec5d530f8f55d` passed both targets and the
full private/generated-inclusive transitive standard-axiom audit, covering all
six modules and 61 actual-origin declarations (35 private). Author-only checks
alone would not have established this result. This guide and the other
release-readiness prose are later documentary changes, not a new checked proof
input; at their September 28, 2026 author checkpoint, the release candidate
still awaits independent acceptance and publication. See the root
README for measured, cache-contextualized build and CI cost guidance.

This generic-field work adapts Beacon's finite-abelian character experiment
(commit `4457d01b7397a1b431bdf0e566f11202227de187`). Its original
incubator author was worker-b Hive Task
`hive-request-463616387133379beaef446d80cf547b5f475217`, UID
`6baba0b3-2702-448c-99b0-87925b4466b1`. Worker-b Hive Task
`hive-request-485dac1da11e46e88fdd51d0c7df9b3e246fdcdb`, UID
`183381ed-5f4a-45d7-a4e9-f6cf0a1889be`, repaired public-module packaging;
this group's adaptation was prepared by
worker-b Hive Task `hive-request-feb04c5ec7b2344e44fa8376f4fe22688559c96a`,
UID `4d2785b4-35e5-40d8-bcbc-ea53c2a89208`. The original mathematical
review and module-repair review apply to their respective exact origin
revisions, not automatically to this destination. Worker-a Hive Task
`hive-request-dcc332f19e575da64ae9054c49c2f761a46ab845`, UID
`4e1208bf-4c98-4bb5-b25a-807a60e37c3b`, supplied the independent static
review of this exact destination; Beacon accepted and integrated it on
September 28, 2026. Worker-b Hive Task
`hive-request-60d57875b5ded531242507f31dc12582d6de02d5`, UID
`fdec958a-3674-4aa5-83c8-3b9969e53193`, prepared this unreviewed
release-readiness documentation successor. The proofs build on native
mathlib character independence, finite duality, matrix rank and complex-basis
ingredients. No source-specific coverage decision follows from this library.
