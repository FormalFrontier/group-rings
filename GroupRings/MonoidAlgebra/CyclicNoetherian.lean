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

These are specializations of the finitely generated commutative-monoid
criterion and its finite-index subgroup form in
`GroupRings.MonoidAlgebra.Noetherian`. Mathlib supplies finite generation of
the integer group and transport along group equivalences. No coefficient
commutativity, nontriviality or subgroup normality premise is imposed.

Import this module directly; `GroupRings` does not re-export it. The public
Laurent Noetherian import is retained for compatibility.

## References

* `GroupRings.MonoidAlgebra.Noetherian`: commutative-monoid and finite-index criteria.
* Mathlib: finite generation of groups and injective group-algebra transport.
* [Multivariate polynomials](https://github.com/FormalFrontier/multivariate-polynomials)
  and [coherent modules](https://github.com/FormalFrontier/coherent-modules):
  the earlier Laurent-ascent proof and its unit-clearing ideal criterion;
  see the library's credits for formalization lineage.
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

/-- The infinite cyclic group algebra is left-Noetherian exactly when its
coefficient ring is, including noncommutative and zero coefficient rings.
This specializes the finitely generated commutative-monoid criterion. -/
theorem isNoetherianRing_multiplicative_int_iff
    {R : Type u} [Ring R] :
    IsNoetherianRing (MonoidAlgebra R (Multiplicative ℤ)) ↔ IsNoetherianRing R :=
  isNoetherianRing_iff_of_fg

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
    IsNoetherianRing (MonoidAlgebra R G) ↔ IsNoetherianRing R := by
  let : IsMulCommutative H := IsMulCommutative.of_comm fun a b =>
    e.injective (by simpa only [map_mul] using mul_comm (e a) (e b))
  let : Group.FG H := Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact isNoetherianRing_iff_of_finiteIndex_comm_fg H

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
