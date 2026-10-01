# Finite-abelian characters and right convolution

Import `GroupRings` to use the character-basis and convolution API from
[`GroupRings.FiniteAbelian.RightConvolution`](../GroupRings/FiniteAbelian/RightConvolution.lean).
The development is algebraic:
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
manifest. From the repository root, install the pinned toolchain and run
`lake exe cache get` **before** `lake build --wfail`. This builds the
`GroupRings` and `GroupRingsTest` default roots, including the six private
ordinary-import Fourier checks in
[`tests/FiniteAbelianRightConvolutionClient.lean`](../tests/FiniteAbelianRightConvolutionClient.lean).
See the [root README](../README.md#reproducible-build-and-checks) for
historical, cache-contextualized cost observations, not performance guarantees.

This generic-field work adapts Beacon's finite-abelian character experiment,
subsequently developed in the incubator and adapted for this library. Mathlib's
character independence, finite duality, matrix rank and complex-basis results
remain distinct upstream contributions; no dependency implementation is copied.
The [root provenance summary](../README.md#references-provenance-and-ai-involvement)
credits the AI-agent contributors. A reusable library result alone makes no
source-specific coverage claim.
