/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.SubgroupIdealsFG
public import GroupRings.MonoidAlgebra.MapDomain
public import GroupRings.RingTheory.Noetherian

/-!
# Left-Noetherian group subalgebras and necessary conditions

For an injective homomorphism from a group `H` into any monoid `M`,
left Noetherianity of `R[M]` descends to `R[H]` over every semiring `R`.
In particular, every subgroup algebra of a left-Noetherian group algebra is
left-Noetherian, with no normality or finite-index assumption. The proof uses
the additive right retraction supplied by coefficient projection, not a ring
homomorphism or a freeness assertion.

If the group algebra over a nontrivial ring is left-Noetherian, every subgroup
of the group is finitely generated. The proof applies the subgroup-ideal
finite-generation criterion to the ordinary left ideal of subgroup differences.
No commutativity or normality assumption is needed.

For any semiring and monoid, the coefficient semiring is a surjective image
under `MonoidAlgebra.augmentation`. Its left-Noetherianity therefore follows
from that of the monoid algebra by Mathlib's `isNoetherianRing_of_surjective`,
using `MonoidAlgebra.augmentation_surjective`. No specialized transport theorem
is needed. These are necessary conditions; no converse is asserted.

Here `IsNoetherianRing A` concerns the left regular module of `A` over itself,
not the group algebra as a module over its coefficient ring.
-/

@[expose] public section

universe u v w

namespace MonoidAlgebra

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

end MonoidAlgebra

/-- Over a nontrivial ring, every subgroup of a group with left-Noetherian group
algebra is finitely generated. The coefficient ring need not be commutative. -/
theorem MonoidAlgebra.subgroup_fg_of_isNoetherianRing
    (R : Type u) [Ring R] [Nontrivial R] {G : Type v} [Group G]
    [IsNoetherianRing (MonoidAlgebra R G)] (H : Subgroup G) : H.FG := by
  exact (MonoidAlgebra.span_subgroup_fg_iff R H).mp (Ideal.fg_of_isNoetherianRing _)
