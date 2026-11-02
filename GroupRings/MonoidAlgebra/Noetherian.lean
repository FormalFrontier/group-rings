/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.SubgroupIdealsFG
public import GroupRings.MonoidAlgebra.MapDomain
public import GroupRings.MonoidAlgebra.SubgroupBasis
public import CoherentModules.RingTheory.Noetherian.Retraction

import Mathlib.Algebra.Group.IsCommutative
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Defs
import MultivariatePolynomials.Noetherian

/-!
# Left-Noetherian monoid algebras and subgroup algebras

For an injective homomorphism from a group `H` into any monoid `M`,
left Noetherianity of `R[M]` descends to `R[H]` over every semiring `R`.
In particular, every subgroup algebra of a left-Noetherian group algebra is
left-Noetherian, with no normality or finite-index assumption. The proof uses
the additive right retraction supplied by coefficient projection, not a ring
homomorphism or a freeness assertion. For a finite-index subgroup and ring
coefficients, the subgroup basis also gives the converse: the two group
algebras are left-Noetherian simultaneously.

If the group algebra over a nontrivial ring is left-Noetherian, every subgroup
of the group is finitely generated. The proof applies the subgroup-ideal
finite-generation criterion to the ordinary left ideal of subgroup differences.
No commutativity or normality assumption is needed.

For any semiring and monoid, the coefficient semiring is a surjective image
under `MonoidAlgebra.augmentation`. Its left-Noetherianity therefore follows
from that of the monoid algebra by Mathlib's `isNoetherianRing_of_surjective`,
using `MonoidAlgebra.augmentation_surjective`. No specialized transport theorem
is needed. For finitely generated commutative monoids and ring coefficients,
the converse holds: a surjective exponent presentation reduces the ascent to
finite-coordinate polynomial Noetherianity. The coefficient ring need not commute.

For a commutative group, the group algebra is left-Noetherian exactly when the
coefficient ring is left-Noetherian and either the coefficient ring is zero or
the group is finitely generated. A finite-index finitely generated commutative
subgroup gives the same coefficient-ring criterion, without requiring the
ambient group to commute or the subgroup to be normal.

Here `IsNoetherianRing A` concerns the left regular module of `A` over itself,
not the group algebra as a module over its coefficient ring.

## References

* `MultivariatePolynomials.Noetherian`: the finite-coordinate theorem
  `AddMonoidAlgebra.isNoetherianRing_finsupp`, used for the commutative-monoid ascent.
-/

@[expose] public section

universe u v w

namespace MonoidAlgebra

/-- A finitely generated commutative monoid algebra over a left-Noetherian ring
is left-Noetherian. The coefficient ring need not be commutative.

The proof uses `AddMonoidAlgebra.isNoetherianRing_finsupp` through a surjective
presentation of the exponent monoid by a finite-coordinate free commutative monoid. -/
theorem isNoetherianRing_of_fg
    (A : Type u) [Ring A] [IsNoetherianRing A]
    (N : Type v) [CommMonoid N] [Monoid.FG N] :
    IsNoetherianRing (MonoidAlgebra A N) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℕ) (M := Additive N)
  let j : Multiplicative (Fin n →₀ ℕ) →* N :=
    AddMonoidHom.toMultiplicativeLeft (Finsupp.linearCombination ℕ s).toAddMonoidHom
  have hj : Function.Surjective j :=
    (span_range_eq_top_iff_surjective_finsuppLinearCombination (R := ℕ) (v := s)).mp hs
  let : IsNoetherianRing (AddMonoidAlgebra A (Fin n →₀ ℕ)) :=
    AddMonoidAlgebra.isNoetherianRing_finsupp A (Fin n)
  let e := AddMonoidAlgebra.toMultiplicative (R := A) (M := Fin n →₀ ℕ)
  exact isNoetherianRing_of_surjective _ _
    ((mapDomainRingHom A j).comp e.toRingHom)
    ((mapDomainRingHom_surjective (R := A) (M := _) (N := N) j hj).comp e.surjective)

/-- A finitely generated commutative monoid algebra is left-Noetherian exactly
when its coefficient ring is left-Noetherian. The coefficient ring may be
noncommutative or zero, and its universe is independent of the monoid's. -/
theorem isNoetherianRing_iff_of_fg
    {R : Type u} [Ring R] {M : Type v} [CommMonoid M] [Monoid.FG M] :
    IsNoetherianRing (MonoidAlgebra R M) ↔ IsNoetherianRing R := by
  constructor
  · intro h
    let := h
    exact isNoetherianRing_of_surjective (MonoidAlgebra R M) R
      (augmentation R M) (augmentation_surjective R M)
  · intro h
    let := h
    exact isNoetherianRing_of_fg R M

/-- A group subalgebra of a left-Noetherian monoid algebra is left-Noetherian.
The coefficient semiring, source group and target monoid have independent
universes. No cancellation in the target monoid is required. -/
theorem isNoetherianRing_of_injective
    {R : Type u} {H : Type v} {M : Type w}
    [Semiring R] [Group H] [Monoid M]
    (j : H →* M) (hj : Function.Injective j)
    [IsNoetherianRing (MonoidAlgebra R M)] :
    IsNoetherianRing (MonoidAlgebra R H) :=
  (mapDomainRingHom R j).isNoetherianRing_of_additive_retraction
    (comapDomainAddMonoidHom j hj) (comapDomain_mapDomain j hj)
    (comapDomain_mul_mapDomain j hj)

/-- Every subgroup algebra of a left-Noetherian group algebra is left-Noetherian,
without normality or finite index, over any coefficient semiring. -/
theorem isNoetherianRing_subgroup
    {R : Type u} {G : Type v} [Semiring R] [Group G]
    [IsNoetherianRing (MonoidAlgebra R G)] (K : Subgroup G) :
    IsNoetherianRing (MonoidAlgebra R K) :=
  isNoetherianRing_of_injective K.subtype Subtype.val_injective

/-- A finite-index subgroup algebra is left-Noetherian if and only if the whole
 group algebra is left-Noetherian, over any coefficient ring. The ascent uses
finiteness as a left module and does not require central scalars or normality. -/
theorem isNoetherianRing_iff_subgroup
    {R : Type u} {G : Type v} [Ring R] [Group G]
    (H : Subgroup G) [H.FiniteIndex] :
    IsNoetherianRing (MonoidAlgebra R G) ↔ IsNoetherianRing (MonoidAlgebra R H) := by
  constructor
  · intro h
    let := h
    exact isNoetherianRing_subgroup H
  · intro h
    let := h
    let := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
    let : IsScalarTower (MonoidAlgebra R H) (MonoidAlgebra R G)
        (MonoidAlgebra R G) := SMul.comp.isScalarTower (mapDomainRingHom R H.subtype)
    let := finite_subgroup (R := R) H
    exact IsNoetherianRing.of_finite (MonoidAlgebra R H) (MonoidAlgebra R G)

end MonoidAlgebra

/-- Over a nontrivial ring, every subgroup of a group with left-Noetherian group
algebra is finitely generated. The coefficient ring need not be commutative. -/
theorem MonoidAlgebra.subgroup_fg_of_isNoetherianRing
    (R : Type u) [Ring R] [Nontrivial R] {G : Type v} [Group G]
    [IsNoetherianRing (MonoidAlgebra R G)] (H : Subgroup G) : H.FG := by
  exact (MonoidAlgebra.span_subgroup_fg_iff R H).mp (Ideal.fg_of_isNoetherianRing _)

namespace MonoidAlgebra

/-- A commutative group algebra is left-Noetherian exactly when its coefficient
ring is left-Noetherian and either that ring is zero or the group is finitely
generated. The coefficient ring need not be commutative, and the coefficient
and group universes are independent. -/
theorem isNoetherianRing_iff_of_commGroup
    {R : Type u} [Ring R] {G : Type v} [CommGroup G] :
    IsNoetherianRing (MonoidAlgebra R G) ↔
      IsNoetherianRing R ∧ (Subsingleton R ∨ Group.FG G) := by
  constructor
  · intro h
    let := h
    refine ⟨isNoetherianRing_of_surjective (MonoidAlgebra R G) R
      (augmentation R G) (augmentation_surjective R G), ?_⟩
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inl hR
    · let := hR
      exact Or.inr (Group.fg_def.mpr (subgroup_fg_of_isNoetherianRing R ⊤))
  · rintro ⟨hR, hzero | hfg⟩
    · let := hzero
      exact isNoetherian_of_subsingleton _ _
    · let := hfg
      exact isNoetherianRing_iff_of_fg.mpr hR

open scoped IsMulCommutative in
/-- A finite-index finitely generated commutative subgroup gives the
left-Noetherian coefficient-ring criterion for the whole group algebra.
Commutativity and finite generation refer to the subgroup's inherited group
operations. Neither ambient commutativity nor normality is required, and the
coefficient ring may be noncommutative or zero. -/
theorem isNoetherianRing_iff_of_finiteIndex_comm_fg
    {R : Type u} [Ring R] {G : Type v} [Group G]
    (H : Subgroup G) [H.FiniteIndex] [IsMulCommutative H] [Group.FG H] :
    IsNoetherianRing (MonoidAlgebra R G) ↔ IsNoetherianRing R :=
  (isNoetherianRing_iff_subgroup (R := R) H).trans isNoetherianRing_iff_of_fg

end MonoidAlgebra
