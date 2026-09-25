/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings

/-!
# Ordinary public-import clients

These private checks exercise only the public aggregate import. The first four
preserve the original development client's examples; the remaining checks cover
the abbreviation, inverse basis laws, degenerate coefficients and algebra laws.
-/

noncomputable section

universe u v w

namespace GroupRingsTest

private def arbitraryCoordinates {A : Type u} [CommSemiring A] {G : Type v}
    [AddCommGroup G] {σ : Type w} (e : G ≃+ (σ →₀ ℤ)) :
    MonoidAlgebra A (Multiplicative G) ≃ₐ[A] MvLaurentPolynomial σ A :=
  e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial

private def emptyIndex {A : Type u} [CommSemiring A] :
    MonoidAlgebra A (Multiplicative (FreeAbelianGroup (Fin 0))) ≃ₐ[A]
      MvLaurentPolynomial (Fin 0) A :=
  FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A (Fin 0)

private def infiniteIndex {A : Type u} [CommSemiring A] :
    MonoidAlgebra A (Multiplicative (FreeAbelianGroup ℕ)) ≃ₐ[A]
      MvLaurentPolynomial ℕ A :=
  FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A ℕ

private theorem generatorSimp (i : Fin 3) (z : ℤ) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial ℤ (Fin 3)
        (MonoidAlgebra.single
          (.ofAdd (FreeAbelianGroup.of i)) z) =
      AddMonoidAlgebra.single (Finsupp.single i 1) z := by
  simp

private theorem semiringModel {A : Type u} [Semiring A] {σ : Type v} :
    MvLaurentPolynomial σ A = AddMonoidAlgebra A (σ →₀ ℤ) := rfl

private def semiringZero {A : Type u} [Semiring A] {σ : Type v} :
    MvLaurentPolynomial σ A := 0

private theorem coordinatesDefinition {A : Type u} [CommSemiring A] {G : Type v}
    [AddCommGroup G] {σ : Type w} (e : G ≃+ (σ →₀ ℤ)) :
    e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial (A := A) =
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv A A G).symm.trans
        (AddMonoidAlgebra.domCongr A A e) := rfl

private theorem canonicalDefinition {A : Type u} [CommSemiring A] {σ : Type v} :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ =
      AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial
        (FreeAbelianGroup.equivFinsupp σ) := rfl

private theorem forwardBasis {A : Type u} [CommSemiring A] {G : Type v}
    [AddCommGroup G] {σ : Type w} (e : G ≃+ (σ →₀ ℤ)) (g : G) (a : A) :
    e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial
        (MonoidAlgebra.single (.ofAdd g) a) =
      AddMonoidAlgebra.single (e g) a :=
  e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial_single g a

private theorem inverseBasis {A : Type u} [CommSemiring A] {G : Type v}
    [AddCommGroup G] {σ : Type w} (e : G ≃+ (σ →₀ ℤ)) (m : σ →₀ ℤ) (a : A) :
    e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial.symm
        (AddMonoidAlgebra.single m a) =
      MonoidAlgebra.single (.ofAdd (e.symm m)) a :=
  e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial_symm_single m a

private theorem canonicalForwardBasis {A : Type u} [CommSemiring A] {σ : Type v}
    (g : FreeAbelianGroup σ) (a : A) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ
        (MonoidAlgebra.single (.ofAdd g) a) =
      AddMonoidAlgebra.single (FreeAbelianGroup.equivFinsupp σ g) a :=
  FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_single A σ g a

private theorem canonicalInverseBasis {A : Type u} [CommSemiring A] {σ : Type v}
    (m : σ →₀ ℤ) (a : A) :
    (FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ).symm
        (AddMonoidAlgebra.single m a) =
      MonoidAlgebra.single (.ofAdd ((FreeAbelianGroup.equivFinsupp σ).symm m)) a :=
  FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_symm_single A σ m a

private theorem canonicalGenerator {A : Type u} [CommSemiring A] {σ : Type v}
    (i : σ) (a : A) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ
        (MonoidAlgebra.single (.ofAdd (FreeAbelianGroup.of i)) a) =
      AddMonoidAlgebra.single (Finsupp.single i 1) a :=
  FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_generator A σ i a

private theorem forwardInverse {A : Type u} [CommSemiring A] {G : Type v}
    [AddCommGroup G] {σ : Type w} (e : G ≃+ (σ →₀ ℤ))
    (f : MvLaurentPolynomial σ A) :
    e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial
        (e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial.symm f) = f :=
  e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial.apply_symm_apply f

private theorem inverseForward {A : Type u} [CommSemiring A] {G : Type v}
    [AddCommGroup G] {σ : Type w} (e : G ≃+ (σ →₀ ℤ))
    (f : MonoidAlgebra A (Multiplicative G)) :
    e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial.symm
        (e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial f) = f :=
  e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial.symm_apply_apply f

private theorem mapSum {A : Type u} [CommSemiring A] {σ : Type v}
    (f g : MonoidAlgebra A (Multiplicative (FreeAbelianGroup σ))) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ (f + g) =
      FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ f +
        FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ g :=
  map_add _ f g

private theorem mapProduct {A : Type u} [CommSemiring A] {σ : Type v}
    (f g : MonoidAlgebra A (Multiplicative (FreeAbelianGroup σ))) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ (f * g) =
      FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ f *
        FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ g :=
  map_mul _ f g

private theorem mapCoefficient {A : Type u} [CommSemiring A] {σ : Type v} (a : A) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ
        (algebraMap A (MonoidAlgebra A (Multiplicative (FreeAbelianGroup σ))) a) =
      algebraMap A (MvLaurentPolynomial σ A) a :=
  AlgEquiv.commutes _ a

private theorem zeroCoefficients {A : Type u} [CommSemiring A] [Subsingleton A]
    {σ : Type v} (f : MonoidAlgebra A (Multiplicative (FreeAbelianGroup σ))) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ f = 0 :=
  Subsingleton.elim _ _

private theorem zeroCoefficientBasis {A : Type u} [CommSemiring A] {σ : Type v}
    (g : FreeAbelianGroup σ) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ
        (MonoidAlgebra.single (.ofAdd g) 0) = 0 := by
  simp

end GroupRingsTest
