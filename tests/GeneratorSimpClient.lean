/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings

/-!
# Bounded generator simplification comparison clients

Ordinary public-import regression clients for the generator simp registration.
The restricted client distinguishes retaining the registration from deleting it.
These are private tests, not new API. The `Fin 0` case is explicitly vacuous.
-/

noncomputable section

universe u v

namespace GeneratorSimpTest

private theorem genericSimp (A : Type u) [CommSemiring A] (σ : Type v)
    (i : σ) (a : A) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ
        (MonoidAlgebra.single (.ofAdd (FreeAbelianGroup.of i)) a) =
      AddMonoidAlgebra.single (Finsupp.single i 1) a := by
  simp

private theorem namedRewrite (A : Type u) [CommSemiring A] (σ : Type v)
    (i : σ) (a : A) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ
        (MonoidAlgebra.single (.ofAdd (FreeAbelianGroup.of i)) a) =
      AddMonoidAlgebra.single (Finsupp.single i 1) a := by
  rw [FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_generator]

private theorem explicitSimpOnly (A : Type u) [CommSemiring A] (σ : Type v)
    (i : σ) (a : A) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ
        (MonoidAlgebra.single (.ofAdd (FreeAbelianGroup.of i)) a) =
      AddMonoidAlgebra.single (Finsupp.single i 1) a := by
  simp only [FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_generator]

private theorem restrictedSimp (A : Type u) [CommSemiring A] (σ : Type v)
    (i : σ) (a : A) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ
        (MonoidAlgebra.single (.ofAdd (FreeAbelianGroup.of i)) a) =
      AddMonoidAlgebra.single (Finsupp.single i 1) a := by
  simp [-FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial_single,
    -AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial_single]

private theorem integerSourceShape (σ : Type v) (i : σ) (z : ℤ) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial ℤ σ
        (MonoidAlgebra.single (.ofAdd (FreeAbelianGroup.of i)) z) =
      AddMonoidAlgebra.single (Finsupp.single i 1) z := by
  simp

private theorem infiniteIndex (A : Type u) [CommSemiring A] (i : ℕ) (a : A) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A ℕ
        (MonoidAlgebra.single (.ofAdd (FreeAbelianGroup.of i)) a) =
      AddMonoidAlgebra.single (Finsupp.single i 1) a := by
  simp

private theorem emptyIndex (A : Type u) [CommSemiring A] (i : Fin 0) (a : A) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A (Fin 0)
        (MonoidAlgebra.single (.ofAdd (FreeAbelianGroup.of i)) a) =
      AddMonoidAlgebra.single (Finsupp.single i 1) a := by
  simp

private theorem zeroSemiring (A : Type u) [CommSemiring A] [Subsingleton A]
    (σ : Type v) (i : σ) (a : A) :
    FreeAbelianGroup.monoidAlgebraEquivMvLaurentPolynomial A σ
        (MonoidAlgebra.single (.ofAdd (FreeAbelianGroup.of i)) a) =
      AddMonoidAlgebra.single (Finsupp.single i 1) a := by
  have ha : a = 0 := Subsingleton.elim _ _
  simpa only [ha] using genericSimp A σ i (0 : A)

end GeneratorSimpTest
