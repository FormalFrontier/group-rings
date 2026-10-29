/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.SubgroupIdealsFG
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Necessary conditions for left-Noetherian group algebras

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

universe u v

/-- Over a nontrivial ring, every subgroup of a group with left-Noetherian group
algebra is finitely generated. The coefficient ring need not be commutative. -/
theorem MonoidAlgebra.subgroup_fg_of_isNoetherianRing
    (R : Type u) [Ring R] [Nontrivial R] {G : Type v} [Group G]
    [IsNoetherianRing (MonoidAlgebra R G)] (H : Subgroup G) : H.FG := by
  exact (MonoidAlgebra.span_subgroup_fg_iff R H).mp (Ideal.fg_of_isNoetherianRing _)
