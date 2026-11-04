/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# Finitely presented commutative monoid algebras

The monoid algebra of a finitely generated commutative monoid is finitely presented
as an algebra over any commutative coefficient ring. The same holds for additive
commutative monoids and `AddMonoidAlgebra`. Neither coefficient Noetherianity nor
cancellation in the exponent monoid is required.

## Implementation notes

The algebra over `ℤ` is of finite type, hence finitely presented because `ℤ` is
Noetherian. Mathlib's finite-presentation base change and `scalarTensorEquiv`
then give the result over arbitrary commutative rings. The additive instance
uses the coefficient-preserving equivalence with the multiplicative type tag.

## References

* Mathlib's `RingTheory.FinitePresentation` (Johan Commelin) and
  `RingTheory.FiniteStability` (Christian Merten) supply finite presentation and
  its stability under base change.
* Mathlib's `RingTheory.TensorProduct.MonoidAlgebra` (Michał Mrugała) supplies
  the scalar base-change equivalence.
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

/-- The algebra of a finitely generated commutative monoid is finitely presented
over any commutative ring, with its canonical coefficient algebra structure. -/
instance finitePresentation_of_fg
    {R : Type u} {M : Type v} [CommRing R] [CommMonoid M] [Monoid.FG M] :
    Algebra.FinitePresentation R (MonoidAlgebra R M) := by
  let : Algebra.FinitePresentation ℤ (MonoidAlgebra ℤ M) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.FinitePresentation.equiv (scalarTensorEquiv ℤ R (M := M))

end MonoidAlgebra

namespace AddMonoidAlgebra

/-- The algebra of a finitely generated additive commutative monoid is finitely
presented over any commutative ring, with its canonical coefficient algebra structure. -/
instance finitePresentation_of_fg
    {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [AddMonoid.FG M] :
    Algebra.FinitePresentation R (AddMonoidAlgebra R M) :=
  Algebra.FinitePresentation.equiv (toMultiplicativeAlgEquiv R R M).symm

end AddMonoidAlgebra
