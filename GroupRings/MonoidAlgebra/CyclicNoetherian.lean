/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.Augmentation
public import GroupRings.MonoidAlgebra.Noetherian
public import MultivariatePolynomials.Laurent.Noetherian

/-!
# Left-Noetherian algebras of cyclic groups and finite extensions

For every coefficient ring, the infinite cyclic group algebra is
left-Noetherian exactly when the coefficient ring is.

The proof uses Mathlib's Laurent model and ring transport, the Laurent
ascent from `multivariate-polynomials`, and the unit-clearing ideal
criterion from `coherent-modules` (Plinth). Group equivalences and
finite-index subgroup extension give the remaining corollaries.
No commutativity, nontriviality or normality premise is imposed.

Import this module directly; `GroupRings` does not re-export it.

## References

* [Multivariate polynomials](https://github.com/FormalFrontier/multivariate-polynomials):
  `LaurentPolynomial.isNoetherianRing_of_isNoetherianRing`.
* [Coherent modules](https://github.com/FormalFrontier/coherent-modules):
  Plinth's unit-clearing ideal criterion.
* Mathlib: `AddMonoidAlgebra.toMultiplicative` and ring-Noetherian transport.
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

/-- The infinite cyclic group algebra is left-Noetherian exactly when its
coefficient ring is, including noncommutative and zero coefficient rings.
The coefficient-to-group implication transports the Laurent ascent from
`multivariate-polynomials`; surjective augmentation gives the group-to-coefficient implication. -/
theorem isNoetherianRing_multiplicative_int_iff
    {R : Type u} [Ring R] :
    IsNoetherianRing (MonoidAlgebra R (Multiplicative ℤ)) ↔ IsNoetherianRing R := by
  constructor
  · intro h
    let := h
    exact isNoetherianRing_of_surjective (MonoidAlgebra R (Multiplicative ℤ)) R
      (augmentation R (Multiplicative ℤ)) (augmentation_surjective R (Multiplicative ℤ))
  · intro h
    let := h
    exact isNoetherianRing_of_ringEquiv (LaurentPolynomial R)
      (AddMonoidAlgebra.toMultiplicative R ℤ)

/-- A supplied equivalence with the infinite cyclic group transports the
coefficient-ring criterion, without changing the coefficient universe. -/
theorem isNoetherianRing_iff_of_mulEquiv_int
    {R : Type u} [Ring R] {G : Type v} [Group G]
    (e : G ≃* Multiplicative ℤ) :
    IsNoetherianRing (MonoidAlgebra R G) ↔ IsNoetherianRing R := by
  constructor
  · intro h
    let := h
    have hz : IsNoetherianRing (MonoidAlgebra R (Multiplicative ℤ)) :=
      isNoetherianRing_of_injective (R := R) e.symm.toMonoidHom e.symm.injective
    exact (isNoetherianRing_multiplicative_int_iff (R := R)).mp hz
  · intro h
    let : IsNoetherianRing (MonoidAlgebra R (Multiplicative ℤ)) :=
      (isNoetherianRing_multiplicative_int_iff (R := R)).mpr h
    exact isNoetherianRing_of_injective (R := R) e.toMonoidHom e.injective

/-- A finite-index infinite cyclic subgroup gives the same left-Noetherian
criterion. The subgroup need not be normal. -/
theorem isNoetherianRing_iff_of_finiteIndex_mulEquiv_int
    {R : Type u} [Ring R] {G : Type v} [Group G]
    (H : Subgroup G) [H.FiniteIndex] (e : H ≃* Multiplicative ℤ) :
    IsNoetherianRing (MonoidAlgebra R G) ↔ IsNoetherianRing R :=
  (isNoetherianRing_iff_subgroup (R := R) H).trans
    (isNoetherianRing_iff_of_mulEquiv_int e)

/-- The product of the infinite cyclic group with a finite group has a
left-Noetherian group algebra exactly when its coefficient ring is left-Noetherian. -/
theorem isNoetherianRing_multiplicative_int_prod_iff
    {R : Type u} [Ring R] {F : Type v} [Group F] [Finite F] :
    IsNoetherianRing (MonoidAlgebra R (Multiplicative ℤ × F)) ↔ IsNoetherianRing R := by
  let π : Multiplicative ℤ × F →* F := MonoidHom.snd _ _
  let H := π.ker
  let : H.FiniteIndex := inferInstance
  let e : H ≃* Multiplicative ℤ :=
    { toFun := fun g => g.1.1
      invFun := fun n => ⟨(n, 1), rfl⟩
      left_inv := fun g => by
        apply Subtype.ext
        exact Prod.ext rfl (show g.1.2 = 1 from g.2).symm
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  exact isNoetherianRing_iff_of_finiteIndex_mulEquiv_int (R := R) H e

end MonoidAlgebra
