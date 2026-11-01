/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.AugmentationNilpotence.Finite

/-!
# Finiteness from augmentation nilpotence

A nilpotent augmentation kernel over a nonzero ring forces the group to be finite,
without a characteristic assumption. Indeed, a nonzero element in the last nonzero
ideal power is fixed by right multiplication by every group basis element. Its
coefficient function is therefore a nonzero constant, so its finite support is the
whole group.

Combining this converse with the prime-characteristic exponent obstruction and the
finite-`p`-group construction gives the classification over arbitrary rings with
`(p : R) = 0`, including the zero ring. Neither the ring nor the group is assumed
commutative.
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

variable {R : Type u} [Ring R] {G : Type v} [Group G]

/-- Nilpotence of the augmentation kernel forces either the coefficient ring to be
zero or the group to be finite. There is no characteristic assumption. -/
theorem subsingleton_or_finite_of_isNilpotent_augmentation
    (h : IsNilpotent (RingHom.ker (augmentation R G))) :
    Subsingleton R ∨ Finite G := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Or.inl hR
  let := hR
  right
  let I : Ideal (MonoidAlgebra R G) := RingHom.ker (augmentation R G)
  obtain ⟨n, hn⟩ := h
  change I ^ n = ⊥ at hn
  suffices ∀ k : ℕ, I ^ k = ⊥ → Finite G from this n hn
  intro k
  induction k with
  | zero =>
    intro hk
    exact (top_ne_bot (by simpa only [Submodule.pow_zero, Ideal.one_eq_top] using hk)).elim
  | succ k ih =>
    intro hk
    by_cases hzero : I ^ k = ⊥
    · exact ih hzero
    obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff (I ^ k)).mp hzero
    have hright (g : G) : a * single g 1 = a := by
      have hg : single g (1 : R) - 1 ∈ I := by
        simp [I, RingHom.mem_ker]
      have hprod := Ideal.mul_mem_mul ha hg
      rw [← Submodule.pow_succ, hk] at hprod
      have hz : a * (single g 1 - 1) = 0 := hprod
      simpa only [mul_sub, mul_one, sub_eq_zero] using hz
    have hcoeff (g : G) : a.coeff g = a.coeff 1 := by
      simpa only [coeff_mul_single_apply, inv_inv, one_mul, mul_one] using
        congrArg (fun x : MonoidAlgebra R G => x.coeff 1) (hright g⁻¹)
    have hcoeff0 : a.coeff 1 ≠ 0 := by
      intro hz
      apply ha0
      apply coeff_injective
      ext g
      simpa only [coeff_zero, Finsupp.zero_apply, hcoeff g] using hz
    apply Finite.of_finite_univ
    apply a.coeff.support.finite_toSet.subset
    intro g _
    exact Finsupp.mem_support_iff.mpr (by simpa only [hcoeff g] using hcoeff0)

/-- For a prime `p` with `(p : R) = 0`, the augmentation kernel is nilpotent exactly
when the coefficient ring is zero or the group is a finite `p`-group. The coefficient
ring may be noncommutative, and the group has no finiteness hypothesis. -/
theorem isNilpotent_augmentation_iff_finite_isPGroup
    {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0) :
    IsNilpotent (RingHom.ker (augmentation R G)) ↔
      Subsingleton R ∨ (Finite G ∧ IsPGroup p G) := by
  constructor
  · intro h
    rcases subsingleton_or_finite_of_isNilpotent_augmentation h with hzero | hfinite
    · exact Or.inl hzero
    rcases subsingleton_or_nontrivial R with hzero | hnonzero
    · exact Or.inl hzero
    let := hnonzero
    exact Or.inr ⟨hfinite, isPGroup_of_isNilpotent_augmentation hp hR h⟩
  · rintro (hzero | ⟨hfinite, hG⟩)
    · let := hzero
      exact ⟨1, Subsingleton.elim _ _⟩
    · let := hfinite
      exact ⟨Nat.card G, augmentation_pow_card_eq_bot hp hR hG⟩

end MonoidAlgebra
