/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn

/-!
# Left ideal powers and ordered products

A power of an ordinary left ideal over a semiring is generated additively by
ordered mixed products of its elements in every positive degree. In degree zero
the ideal power is the top ideal, while the empty product is one; left-ideal
closure makes the same universal property valid in that degree as well.

The proofs reuse Mathlib's additive-submonoid powers and their description as
additive closures of pointwise set powers. No two-sidedness is needed.
-/

@[expose] public section

universe u

namespace Ideal

variable {A : Type u} [Semiring A] {I J : Ideal A}

/-- An ordered product of elements of a left ideal belongs to the power whose
degree is the length of the list, including the empty product in degree zero. -/
theorem list_prod_mem_pow (l : List A) (hl : ∀ x ∈ l, x ∈ I) :
    l.prod ∈ I ^ l.length := by
  apply Submodule.pow_subset_pow I
  apply Set.mem_pow.mpr
  refine ⟨fun i => ⟨l.get i, hl _ (List.get_mem _ _)⟩, ?_⟩
  simp only [List.ofFn_get]

/-- A left ideal contains a power exactly when it contains every ordered mixed
product of that length. This also holds in degree zero, where containing the
empty product forces the target ideal to be top. -/
theorem pow_le_iff_forall_list_prod_mem (n : ℕ) :
    I ^ n ≤ J ↔ ∀ l : List A, l.length = n → (∀ x ∈ l, x ∈ I) → l.prod ∈ J := by
  constructor
  · intro h l hn hl
    exact h (hn ▸ list_prod_mem_pow l hl)
  · intro h
    obtain rfl | hn := eq_or_ne n 0
    · have h1 : (1 : A) ∈ J := h [] rfl (by simp)
      intro x _
      simpa only [mul_one] using J.mul_mem_left x h1
    · change (I ^ n).toAddSubmonoid ≤ J.toAddSubmonoid
      rw [Submodule.pow_toAddSubmonoid I hn, AddSubmonoid.pow_eq_closure_pow_set,
        Submodule.coe_toAddSubmonoid, AddSubmonoid.closure_le]
      intro a ha
      obtain ⟨f, rfl⟩ := Set.mem_pow.mp ha
      apply h _ List.length_ofFn
      rw [List.forall_mem_ofFn_iff]
      exact fun i => SetLike.mem_coe.mp (f i).property

/-- A power of a left ideal is zero exactly when every ordered mixed product of
that length vanishes. For degree zero both sides express `1 = 0`. -/
theorem pow_eq_bot_iff_forall_list_prod_eq_zero (I : Ideal A) (n : ℕ) :
    I ^ n = ⊥ ↔ ∀ l : List A, l.length = n → (∀ x ∈ l, x ∈ I) → l.prod = 0 := by
  rw [← le_bot_iff, pow_le_iff_forall_list_prod_mem]
  simp only [mem_bot]

end Ideal
