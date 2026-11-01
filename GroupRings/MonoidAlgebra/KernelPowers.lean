/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.NoncommRing

public import GroupRings.MonoidAlgebra.CoefficientIdeals
public import GroupRings.RingTheory.Ideal.Powers

/-!
# Powers of coefficient kernels

Coefficient change in a monoid algebra preserves and reflects the vanishing of
kernel powers, at each fixed exponent. The coefficient semirings may be
noncommutative or zero, and the indexing monoid may be infinite.
-/

@[expose] public section

universe u v w

namespace MonoidAlgebra

variable {R : Type u} {S : Type v} {M : Type w}
variable [Semiring R] [Semiring S] [Monoid M]

private theorem single_mul_list_prod_eq_zero_of_coeff_prod_eq_zero
    (l : List R[M]) (m : M) (r : R)
    (h : ∀ g : Fin l.length → M,
      r * (List.ofFn (fun i => (l.get i).coeff (g i))).prod = 0) :
    single m r * l.prod = 0 := by
  classical
  induction l generalizing m r with
  | nil =>
      have hr : r = 0 := by simpa using h (fun _ => 1)
      simp [hr]
  | cons a l ih =>
      -- Expand the head itself; vanishing of a sum does not imply vanishing of its terms.
      have ha : (∑ k ∈ a.coeff.support, single k (a.coeff k)) = a := by
        apply coeff_injective
        ext k
        by_cases hk : a.coeff k = 0 <;> simp [Finsupp.single_apply, hk]
      have hz : ∀ k : M, single (m * k) (r * a.coeff k) * l.prod = 0 := by
        intro k
        apply ih
        intro g
        have hkg : r * (a.coeff k *
            (List.ofFn (fun i => (l.get i).coeff (g i))).prod) = 0 := by
          simpa using h (Fin.cons k g)
        calc
          (r * a.coeff k) * (List.ofFn (fun i => (l.get i).coeff (g i))).prod =
              r * (a.coeff k *
                (List.ofFn (fun i => (l.get i).coeff (g i))).prod) := by noncomm_ring
          _ = 0 := hkg
      calc
        single m r * (a :: l).prod = single m r * (a * l.prod) := by simp
        _ = (single m r * a) * l.prod := by noncomm_ring
        _ = (single m r * ∑ k ∈ a.coeff.support, single k (a.coeff k)) * l.prod := by
          rw [ha]
        _ = ∑ k ∈ a.coeff.support, single (m * k) (r * a.coeff k) * l.prod := by
          rw [Finset.mul_sum, Finset.sum_mul]
          simp
        _ = 0 := by simp [hz]

private theorem list_prod_eq_zero_of_coeff_prod_eq_zero (l : List R[M])
    (h : ∀ g : Fin l.length → M,
      (List.ofFn (fun i => (l.get i).coeff (g i))).prod = 0) :
    l.prod = 0 := by
  have hprefix : ∀ g : Fin l.length → M,
      (1 : R) * (List.ofFn (fun i => (l.get i).coeff (g i))).prod = 0 := by
    intro g
    simpa using h g
  have hunit : single (1 : M) (1 : R) = (1 : R[M]) := by rfl
  have hzero :=
    single_mul_list_prod_eq_zero_of_coeff_prod_eq_zero l (1 : M) (1 : R) hprefix
  rw [hunit] at hzero
  simpa using hzero

private theorem coeff_products_eq_zero_of_mem_ker_mapRingHom
    (f : R →+* S) (n : ℕ) (h : RingHom.ker f ^ n = ⊥)
    (l : List (R[M])) (hl : l.length = n)
    (hker : ∀ x ∈ l, x ∈ RingHom.ker (mapRingHom M f))
    (g : Fin l.length → M) :
    (List.ofFn fun i => (l.get i).coeff (g i)).prod = 0 := by
  apply (Ideal.pow_eq_bot_iff_forall_list_prod_eq_zero (RingHom.ker f) n).mp h
    (List.ofFn fun i => (l.get i).coeff (g i))
  · simpa using hl
  · refine List.forall_mem_ofFn_iff.mpr ?_
    intro i
    exact (mapRingHom_eq_zero_iff f (l.get i)).mp
      (RingHom.mem_ker.mp ((List.forall_mem_iff_get.mp hker) i)) (g i)

private theorem ker_pow_eq_bot_of_ker_mapRingHom_pow_eq_bot (f : R →+* S) (n : ℕ)
    (h : RingHom.ker (mapRingHom M f) ^ n = ⊥) : RingHom.ker f ^ n = ⊥ := by
  classical
  apply (Ideal.pow_eq_bot_iff_forall_list_prod_eq_zero (RingHom.ker f) n).2
  intro l hl hmem
  have hsingle : ∀ r ∈ l,
      single (1 : M) r ∈ RingHom.ker (mapRingHom M f) := by
    intro r hr
    apply (RingHom.mem_ker).2
    apply (mapRingHom_eq_zero_iff f _).2
    intro m
    by_cases hm : m = (1 : M)
    · subst m
      simpa using hmem r hr
    · simp [hm]
  have hprod : (l.map (fun r : R => single (1 : M) r)).prod = 0 := by
    apply (Ideal.pow_eq_bot_iff_forall_list_prod_eq_zero
      (RingHom.ker (mapRingHom M f)) n).1 h
    · simpa using hl
    · intro x hx
      obtain ⟨r, hr, rfl⟩ :
          ∃ r : R, r ∈ l ∧ single (1 : M) r = x := by
        simpa using hx
      exact hsingle r hr
  have hconstant (L : List R) :
      (L.map (fun r : R => single (1 : M) r)).prod = single (1 : M) L.prod := by
    induction L with
    | nil => rfl
    | cons r L ih => simp [ih]
  rw [hconstant l] at hprod
  have hcoeff : (single (1 : M) l.prod).coeff (1 : M) = 0 := by
    rw [hprod]
    simp
  simpa using hcoeff

/-- The kernel of coefficient change has a vanishing power at exactly the same
exponents as the coefficient homomorphism. This includes exponent zero. -/
@[simp] theorem ker_mapRingHom_pow_eq_bot_iff (f : R →+* S) (n : ℕ) :
    RingHom.ker (mapRingHom M f) ^ n = ⊥ ↔ RingHom.ker f ^ n = ⊥ := by
  constructor
  · exact ker_pow_eq_bot_of_ker_mapRingHom_pow_eq_bot f n
  · intro h
    apply (Ideal.pow_eq_bot_iff_forall_list_prod_eq_zero
      (RingHom.ker (mapRingHom M f)) n).mpr
    intro l hl hker
    exact list_prod_eq_zero_of_coeff_prod_eq_zero l
      (coeff_products_eq_zero_of_mem_ker_mapRingHom f n h l hl hker)

end MonoidAlgebra
