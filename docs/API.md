# Generated API reference

Historical four-module snapshot: eight authored public Laurent declarations,
not all public declarations of the current group-rings library.
Import `GroupRings`; its leaf is `GroupRings.FreeAbelian.LaurentPolynomial`.
`PublicAPIClient` and `GeneratorSimpClient` contain private checked clients, not public API.

The separate Fourier character, basis and right-convolution results are documented in
the [handwritten Fourier guide](FiniteAbelianRightConvolution.md); see also the
[current mathematical overview](../README.md#headline-results).

The compiled environment also exposes the generated equation lemma
`AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial.eq_1` for the
coordinate definition. Native doc-gen4 does not list it as an authored declaration.
This page is not a private/generated-declaration census or proof audit.

Headers below are native doc-gen4 display signatures, not complete declarations
with proof bodies. Short names use the source's `AddEquiv` or `FreeAbelianGroup`
namespace, `open Multiplicative` and imports. Implicit parameters are displayed;
`u`, `v` and `w` are universes. Source links target this same checkout.

The [historical manifest](api-manifest.json) binds the original four-module native
records and source/pin inputs, not a new analysis of the current expanded root.
This page's preamble is a presentation update; its eight signatures, docstrings
and source anchors remain the retained historical output. Replay needs the exact
old sources and native records; see [generation instructions](README.md).

## MvLaurentPolynomial

```lean
abbrev MvLaurentPolynomial (σ : Type u) (A : Type v) [Semiring A] : Type (max v u)
```

Multivariable Laurent polynomials with variables indexed by `σ` and
coefficients in `A`.

[Source](../GroupRings/FreeAbelian/LaurentPolynomial.lean#L24) (line 24).

## AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial

```lean
noncomputable def AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial {A : Type u} {G : Type v} {σ : Type w} [CommSemiring A] [AddCommGroup G] (e : G ≃+ (σ →₀ ℤ)) : MonoidAlgebra A (Multiplicative G) ≃ₐ[A] MvLaurentPolynomial σ A
```

Additive coordinates on a group induce an algebra equivalence from its
group algebra to the corresponding multivariable Laurent polynomial algebra.

[Source](../GroupRings/FreeAbelian/LaurentPolynomial.lean#L33) (line 33).

## AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial_single

```lean
theorem AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial_single {A : Type u} {G : Type v} {σ : Type w} [CommSemiring A] [AddCommGroup G] (e : G ≃+ (σ →₀ ℤ)) (g : G) (a : A) : e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial (MonoidAlgebra.single (Multiplicative.ofAdd g) a) = AddMonoidAlgebra.single (e g) a
```

Supplied additive coordinates send a group-algebra basis term at `g` to the
Laurent basis term with exponent vector `e g`, preserving its coefficient.

[Source](../GroupRings/FreeAbelian/LaurentPolynomial.lean#L41) (line 41).

## AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial_symm_single

```lean
theorem AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial_symm_single {A : Type u} {G : Type v} {σ : Type w} [CommSemiring A] [AddCommGroup G] (e : G ≃+ (σ →₀ ℤ)) (m : σ →₀ ℤ) (a : A) : e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial.symm (AddMonoidAlgebra.single m a) = MonoidAlgebra.single (Multiplicative.ofAdd (e.symm m)) a
```

The inverse coordinate equivalence sends a Laurent basis term at `m` to
the group-algebra basis term at `e.symm m`, preserving its coefficient.

[Source](../GroupRings/FreeAbelian/LaurentPolynomial.lean#L57) (line 57).

## FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial

```lean
noncomputable def FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial (A : Type u) [CommSemiring A] (σ : Type v) : MonoidAlgebra A (Multiplicative (FreeAbelianGroup σ)) ≃ₐ[A] MvLaurentPolynomial σ A
```

The group algebra of the free abelian group on `σ` is the multivariable
Laurent polynomial algebra on `σ`.

[Source](../GroupRings/FreeAbelian/LaurentPolynomial.lean#L74) (line 74).

## FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_single

```lean
theorem FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_single (A : Type u) [CommSemiring A] (σ : Type v) (g : FreeAbelianGroup σ) (a : A) : (monoidAlgebraEquivMvLaurentPolynomial A σ) (MonoidAlgebra.single (Multiplicative.ofAdd g) a) = AddMonoidAlgebra.single ((equivFinsupp σ) g) a
```

The canonical free-abelian equivalence sends a basis term at `g` to the
Laurent basis term whose exponent vector is `equivFinsupp σ g`.

[Source](../GroupRings/FreeAbelian/LaurentPolynomial.lean#L81) (line 81).

## FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_symm_single

```lean
theorem FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_symm_single (A : Type u) [CommSemiring A] (σ : Type v) (m : σ →₀ ℤ) (a : A) : (monoidAlgebraEquivMvLaurentPolynomial A σ).symm (AddMonoidAlgebra.single m a) = MonoidAlgebra.single (Multiplicative.ofAdd ((equivFinsupp σ).symm m)) a
```

The inverse canonical equivalence sends a Laurent basis term at `m` to the
free-abelian group element with coordinates `m`, preserving its coefficient.

[Source](../GroupRings/FreeAbelian/LaurentPolynomial.lean#L92) (line 92).

## FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_generator

```lean
theorem FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_generator (A : Type u) [CommSemiring A] (σ : Type v) (i : σ) (a : A) : (monoidAlgebraEquivMvLaurentPolynomial A σ) (MonoidAlgebra.single (Multiplicative.ofAdd (of i)) a) = AddMonoidAlgebra.single (Finsupp.single i 1) a
```

A basis term at the free generator `of i` has exponent one at `i` and zero
elsewhere. Its coefficient is unchanged. The specialized simp rule has priority
1100, before the general single-term rules.

[Source](../GroupRings/FreeAbelian/LaurentPolynomial.lean#L103) (line 103).
