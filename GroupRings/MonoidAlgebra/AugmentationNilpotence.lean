/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.Augmentation
public import GroupRings.RingTheory.Ideal.Powers
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.GroupTheory.PGroup

/-!
# Uniform group exponents from augmentation nilpotence

Over a nontrivial ring with `p = 0` for prime `p`, nilpotence of the coefficient-sum
augmentation kernel forces one common `p`-power exponent for every group element.
Neither the ring nor the group is assumed commutative, and the group need not be
finite. The same conclusion holds for uniform vanishing of ordered mixed products.

For a single power `p ^ k` at least the nilpotence degree, Mathlib's ideal-power
API kills `(single g 1 - 1) ^ (p ^ k)`. Its commuting binomial identity in prime
characteristic identifies this with `single (g ^ (p ^ k)) 1 - 1`. Injectivity of
the basis embedding then recovers the group equation. Only commutation with one
is used, not commutativity of the group ring.

This module does not prove the converse implication for finite `p`-groups, its
exact cardinality bound, or a finite-group equivalence.
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

variable {R : Type u} [Ring R] [Nontrivial R] {G : Type v} [Group G]
variable {p n k : ℕ}

/-- If the augmentation kernel has vanishing `n`-th power, every `p ^ k` at
least `n` is a common exponent for the group, over a nontrivial ring with
`p = 0` for prime `p`. -/
theorem forall_pow_eq_one_of_augmentation_pow_eq_bot (hp : p.Prime) (hR : (p : R) = 0)
    (hn : (RingHom.ker (augmentation R G)) ^ n = ⊥) (hnk : n ≤ p ^ k) :
    ∀ g : G, g ^ (p ^ k) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (MonoidAlgebra R G) p :=
    (CharP.charP_iff_prime_eq_zero hp).mpr (by
      rw [← map_natCast (singleOneRingHom (R := R) (M := G)) p, hR, map_zero])
  intro g
  have hx : single g (1 : R) - 1 ∈ RingHom.ker (augmentation R G) := by
    simp [RingHom.mem_ker]
  have hz := Ideal.pow_eq_zero_of_mem hn hnk hx
  rw [sub_pow_char_pow_of_commute p k (Commute.one_right _), one_pow] at hz
  apply of_injective (R := R) (M := G)
  simpa [one_def] using sub_eq_zero.mp hz

/-- Nilpotence of the canonical augmentation ideal forces a uniform `p`-power
exponent, even for an infinite group. This is stronger than `IsPGroup p G`. -/
theorem exists_pow_eq_one_of_isNilpotent_augmentation (hp : p.Prime) (hR : (p : R) = 0)
    (hI : IsNilpotent (RingHom.ker (augmentation R G))) :
    ∃ k : ℕ, ∀ g : G, g ^ (p ^ k) = 1 := by
  obtain ⟨n, hn⟩ := hI
  exact ⟨n, forall_pow_eq_one_of_augmentation_pow_eq_bot hp hR hn
    (Nat.lt_pow_self hp.one_lt).le⟩

/-- Uniform vanishing of mixed ordered products in the augmentation ideal
forces one common `p`-power exponent for the group, without finiteness. -/
theorem exists_pow_eq_one_of_augmentation_products_eq_zero (hp : p.Prime)
    (hR : (p : R) = 0)
    (hI : ∃ n : ℕ, ∀ l : List (MonoidAlgebra R G), l.length = n →
      (∀ x ∈ l, x ∈ RingHom.ker (augmentation R G)) → l.prod = 0) :
    ∃ k : ℕ, ∀ g : G, g ^ (p ^ k) = 1 := by
  obtain ⟨n, hn⟩ := hI
  exact exists_pow_eq_one_of_isNilpotent_augmentation hp hR
    ⟨n, (Ideal.pow_eq_bot_iff_forall_list_prod_eq_zero _ n).mpr hn⟩

/-- A group whose augmentation ideal is nilpotent over a nontrivial ring with
`p = 0` for prime `p` is a `p`-group. No finiteness assumption is needed. -/
theorem isPGroup_of_isNilpotent_augmentation (hp : p.Prime) (hR : (p : R) = 0)
    (hI : IsNilpotent (RingHom.ker (augmentation R G))) : IsPGroup p G := by
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isNilpotent_augmentation hp hR hI
  exact fun g => ⟨k, hk g⟩

end MonoidAlgebra
