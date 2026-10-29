/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings

/-!
# Left-Noetherian necessary conditions through the public import

Coefficient descent uses the stock generic surjective-homomorphism theorem,
without a coefficient commutativity or nontriviality assumption. The group
conclusion applies to every subgroup without a normality or prior FG premise.
-/

universe u v

private theorem coefficient_noetherian
    (R : Type u) [Semiring R] (M : Type v) [Monoid M]
    [IsNoetherianRing (MonoidAlgebra R M)] : IsNoetherianRing R :=
  isNoetherianRing_of_surjective (MonoidAlgebra R M) R
    (MonoidAlgebra.augmentation R M) (MonoidAlgebra.augmentation_surjective R M)

private theorem every_subgroup_fg
    (R : Type u) [Ring R] [Nontrivial R] {G : Type v} [Group G]
    [IsNoetherianRing (MonoidAlgebra R G)] (H : Subgroup G) : H.FG :=
  MonoidAlgebra.subgroup_fg_of_isNoetherianRing R H
