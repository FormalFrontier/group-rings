/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Centrality of idempotents along nilpotent ideal powers

An idempotent that is central modulo a nilpotent two-sided ideal is central if both
cross-corner maps send the ideal into its square. Each of these first-layer conditions
propagates to all positive powers, independently of nilpotence or quotient centrality.
Iteration then kills the two cross-corners of every ring element.
-/

@[expose] public section

namespace IsIdempotentElem

variable {A : Type*} [Ring A]

/-- If one off-diagonal corner raises the first ideal layer, it raises every
positive layer of the ideal-power filtration. -/
theorem mul_mul_one_sub_mem_pow_succ {I : Ideal A} [I.IsTwoSided] {e : A}
    (he : IsIdempotentElem e)
    (h : ∀ x ∈ I, e * x * (1 - e) ∈ I ^ 2)
    (n : ℕ) {x : A} (hx : x ∈ I ^ (n + 1)) :
    e * x * (1 - e) ∈ I ^ (n + 2) := by
  let f : A := 1 - e
  have hf : IsIdempotentElem f := he.one_sub
  have hsum : e + f = 1 := by
    dsimp [f]
    rw [add_comm, sub_add_cancel]
  have hfirst : ∀ y ∈ I, e * y * f ∈ I ^ 2 := h
  -- Insert the two complementary diagonal corners between the factors.
  have hsplit (a b : A) :
      e * (a * b) * f =
        (e * a * e) * (e * b * f) + (e * a * f) * (f * b * f) := by
    calc
      e * (a * b) * f = e * a * (e + f) * b * f := by
        rw [hsum]
        simp only [mul_one, mul_assoc]
      _ = (e * a * e) * (e * b * f) + (e * a * f) * (f * b * f) := by
        simp only [mul_add, add_mul, mul_assoc, he.mul_self_mul, hf.mul_self_mul]
  change e * x * f ∈ I ^ (n + 2)
  induction n generalizing x with
  | zero =>
      exact hfirst x (by simpa only [Nat.zero_add, Submodule.pow_one] using hx)
  | succ n ih =>
      change x ∈ I ^ ((n + 1) + 1) at hx
      rw [Submodule.pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        have hdiagA : e * a * e ∈ I ^ (n + 1) :=
          (I ^ (n + 1)).mul_mem_right e ((I ^ (n + 1)).mul_mem_left e ha)
        have hdiagB : f * b * f ∈ I :=
          I.mul_mem_right f (I.mul_mem_left f hb)
        have hleft : (e * a * e) * (e * b * f) ∈ I ^ ((n + 1) + 2) := by
          rw [Ideal.IsTwoSided.pow_add]
          exact Ideal.mul_mem_mul hdiagA (hfirst b hb)
        have hright : (e * a * f) * (f * b * f) ∈ I ^ ((n + 1) + 2) := by
          change (e * a * f) * (f * b * f) ∈ I ^ ((n + 2) + 1)
          rw [Submodule.pow_succ]
          exact Ideal.mul_mem_mul (ih ha) hdiagB
        rw [hsplit]
        exact (I ^ ((n + 1) + 2)).add_mem hleft hright
      · intro a b ha hb
        simpa only [mul_add, add_mul] using (I ^ ((n + 1) + 2)).add_mem ha hb

private lemma eq_zero_of_mem_of_pow_step (I : Ideal A) (hI : IsNilpotent I)
    {x : A} (hx : x ∈ I)
    (hstep : ∀ n : ℕ, x ∈ I ^ (n + 1) → x ∈ I ^ (n + 2)) : x = 0 := by
  have hall (n : ℕ) : x ∈ I ^ (n + 1) := by
    induction n with
    | zero => simpa only [Nat.zero_add, Submodule.pow_one] using hx
    | succ n ih => exact hstep n ih
  obtain ⟨n, hn⟩ := hI
  have h : x ∈ I ^ n := Ideal.pow_le_pow_right (Nat.le_succ n) (hall n)
  rw [hn] at h
  exact h

/-- An idempotent central modulo a nilpotent two-sided ideal is central if both of its
cross-corner maps send the ideal into its square.

No commutativity or nontriviality of the ring is required. -/
theorem isMulCentral_of_sandwich_mem_sq {I : Ideal A} [I.IsTwoSided] {e : A}
    (he : IsIdempotentElem e) (hI : IsNilpotent I)
    (hc : IsMulCentral (Ideal.Quotient.mk I e))
    (hleft : ∀ x ∈ I, e * x * (1 - e) ∈ I ^ 2)
    (hright : ∀ x ∈ I, (1 - e) * x * e ∈ I ^ 2) :
    IsMulCentral e := by
  refine ⟨fun a ↦ ?_, fun _ _ ↦ (mul_assoc _ _ _).symm, fun _ _ ↦ mul_assoc _ _ _⟩
  have hcomm : e * a - a * e ∈ I := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    simpa only [map_mul] using (hc.comm (Ideal.Quotient.mk I a)).eq
  have hp : e * a * (1 - e) ∈ I := by
    simpa only [sub_mul, mul_assoc, he.mul_one_sub_self, mul_zero, sub_zero] using
      Ideal.mul_mem_right (1 - e) I hcomm
  have hq : (1 - e) * a * e ∈ I := by
    have hcomm' : a * e - e * a ∈ I := by
      simpa only [neg_sub] using I.neg_mem hcomm
    simpa only [mul_sub, ← mul_assoc, he.one_sub_mul_self, zero_mul, sub_zero] using
      I.mul_mem_left (1 - e) hcomm'
  have hpfix : e * (e * a * (1 - e)) * (1 - e) = e * a * (1 - e) := by
    calc
      _ = (e * e) * a * ((1 - e) * (1 - e)) := by simp only [mul_assoc]
      _ = _ := by rw [he.eq, he.one_sub.eq]
  have hqfix : (1 - e) * ((1 - e) * a * e) * e = (1 - e) * a * e := by
    calc
      _ = ((1 - e) * (1 - e)) * a * (e * e) := by simp only [mul_assoc]
      _ = _ := by rw [he.one_sub.eq, he.eq]
  have hpzero : e * a * (1 - e) = 0 :=
    eq_zero_of_mem_of_pow_step I hI hp fun n hx ↦ by
      simpa only [hpfix] using he.mul_mul_one_sub_mem_pow_succ hleft n hx
  have hqzero : (1 - e) * a * e = 0 :=
    eq_zero_of_mem_of_pow_step I hI hq fun n hx ↦ by
      have hright' : ∀ x ∈ I, (1 - e) * x * (1 - (1 - e)) ∈ I ^ 2 := by
        simpa only [sub_sub_cancel] using hright
      simpa only [sub_sub_cancel, hqfix] using
        he.one_sub.mul_mul_one_sub_mem_pow_succ hright' n hx
  have hp' : e * a = e * a * e :=
    sub_eq_zero.mp (by simpa only [mul_sub, mul_one] using hpzero)
  have hq' : a * e = e * a * e :=
    sub_eq_zero.mp (by simpa only [sub_mul, one_mul] using hqzero)
  exact hp'.trans hq'.symm

end IsIdempotentElem
