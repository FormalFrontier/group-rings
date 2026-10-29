/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings

/-!
# Descending a representation to a quotient group ring

A ring homomorphism trivial on the subgroup basis units descends, and its
values on arbitrary coefficients can be recovered without unfolding the lift.
The coefficient ring, group, and semiring target have independent universes.
-/

universe u v w

open MonoidAlgebra

example (R : Type u) [Ring R] {G : Type v} [Group G]
    (N : Subgroup G) [N.Normal] {S : Type w} [Semiring S]
    (θ : MonoidAlgebra R G →+* S)
    (hθ : ∀ n : N, θ (single (n : G) 1) = 1) :
    ∃ ψ : MonoidAlgebra R (G ⧸ N) →+* S,
      ψ.comp (mapDomainRingHom R (QuotientGroup.mk' N)) = θ ∧
      ∀ (g : G) (r : R),
        ψ (single (QuotientGroup.mk' N g) r) = θ (single g r) := by
  obtain ⟨ψ, hψ, _⟩ := (existsUnique_comp_mapDomainRingHom_mk'_iff R N θ).mpr hθ
  exact ⟨ψ, hψ, comp_mapDomainRingHom_mk'_single R N θ ψ hψ⟩
