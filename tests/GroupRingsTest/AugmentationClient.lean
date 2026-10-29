/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings

/-!
# Augmentation-kernel elements and left multiplication

The generator corresponding to the positive generator of the additive natural
numbers augments to zero but is not zero in the monoid algebra over the integers.
The span theorem also handles arbitrary left coefficients and left monoid indices,
without commuting either multiplication.
-/

open MonoidAlgebra

noncomputable section

universe u v

example :
    (single (Multiplicative.ofAdd (1 : ℕ)) (1 : ℤ) - 1 :
      MonoidAlgebra ℤ (Multiplicative ℕ)) ∈
        RingHom.ker (augmentation ℤ (Multiplicative ℕ)) ∧
    (single (Multiplicative.ofAdd (1 : ℕ)) (1 : ℤ) - 1 :
      MonoidAlgebra ℤ (Multiplicative ℕ)) ≠ 0 := by
  constructor
  · simp [RingHom.mem_ker]
  · intro h
    have hcoeff := congrArg
      (fun x : MonoidAlgebra ℤ (Multiplicative ℕ) =>
        x.coeff (Multiplicative.ofAdd (1 : ℕ))) h
    simp [MonoidAlgebra.one_def] at hcoeff

example (R : Type u) (M : Type v) [Ring R] [Monoid M] (r : R) (m n : M) :
    (single (n * m) r - single n r : MonoidAlgebra R M) ∈
      RingHom.ker (augmentation R M) := by
  rw [ker_augmentation]
  have hgen : single m (1 : R) - 1 ∈
      Ideal.span (Set.range (fun m : M => single m (1 : R) - 1)) :=
    Ideal.subset_span ⟨m, rfl⟩
  simpa [mul_sub] using (Ideal.span _).mul_mem_left (single n r) hgen
