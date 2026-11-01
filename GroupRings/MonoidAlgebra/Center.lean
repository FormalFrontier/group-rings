/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Centers of group algebras

Coefficient centrality and conjugation invariance characterize the center of a group algebra.
The coefficient condition also applies to monoid algebras. Nonzero coefficients of central
elements have finite conjugation orbits.

The center, coefficient map, and conjugation action are those of Mathlib.

For commutative-ring coefficients, the ordinary-center specialization of Manju and Sharma,
Lemma 4.12, describes central elements by finite conjugacy-class sums. The coefficient criterion
and finite-support consequences here are proved directly for arbitrary semirings, retaining
coefficient centrality when the coefficients do not commute. Both twists in the cited result are
specialized to the identity; no twisted-center or class-sum basis construction is asserted here.

## References

* Praveen Manju and Rajendra Kumar Sharma, *(σ, τ)-Derivations of Group Rings with Applications*,
  arXiv:2303.04372v3 (2024), §4.2, Lemma 4.12,
  [online](https://arxiv.org/html/2303.04372v3#S4.Thmtheorem12).
-/

@[expose] public section

universe u v w

namespace MonoidAlgebra

section Monoid

variable {R : Type u} {M : Type w} [Semiring R] [Monoid M]

/-- Every coefficient of a central monoid-algebra element is central in the coefficient semiring. -/
theorem coeff_mem_center {z : R[M]} (hz : z ∈ Subsemiring.center (R[M])) (m : M) :
    z.coeff m ∈ Subsemiring.center R := by
  classical
  apply Subsemiring.mem_center_iff.mpr
  intro r
  let ev : R[M] →+ R :=
    { toFun := fun x => x.coeff m
      map_zero' := by simp
      map_add' := by intro x y; simp }
  have ev_apply (x : R[M]) : ev x = x.coeff m := rfl
  -- Evaluate multiplication by a scalar monomial using additive single-term extensionality.
  have hl : ev.comp (AddMonoidHom.mulLeft (single 1 r : R[M])) =
      (AddMonoidHom.mulLeft r).comp ev := by
    apply addMonoidHom_ext
    intro n s
    by_cases h : n = m <;> simp [ev_apply, h]
  have hr : ev.comp (AddMonoidHom.mulRight (single 1 r : R[M])) =
      (AddMonoidHom.mulRight r).comp ev := by
    apply addMonoidHom_ext
    intro n s
    by_cases h : n = m <;> simp [ev_apply, h]
  calc
    r * z.coeff m = ev (single 1 r * z) := by
      simpa [ev_apply] using
        (congrArg (fun f : R[M] →+ R => f z) hl).symm
    _ = ev (z * single 1 r) :=
      congrArg ev (Subsemiring.mem_center_iff.mp hz (single 1 r))
    _ = z.coeff m * r := by
      simpa [ev_apply] using congrArg (fun f : R[M] →+ R => f z) hr

end Monoid

section Group

variable {R : Type u} {G : Type v} [Semiring R] [Group G]

/-- A group-algebra element is central exactly when its coefficients are central and invariant
under conjugation.

For a class-sum description over commutative rings, compare the identity-twist case of
Manju and Sharma, Lemma 4.12 (see the module references). The present criterion is proved
directly over arbitrary semirings, with coefficient centrality explicit. -/
theorem mem_center_iff (z : R[G]) :
    z ∈ Subsemiring.center (R[G]) ↔
      (∀ g : G, z.coeff g ∈ Subsemiring.center R) ∧
        (∀ h g : G, z.coeff (h * g * h⁻¹) = z.coeff g) := by
  classical
  constructor
  · intro hz
    refine ⟨coeff_mem_center hz, ?_⟩
    intro h g
    -- Test commutation with the basis element at h, at coefficient h * g.
    simpa [mul_assoc] using
      (congrArg (fun x : R[G] => x.coeff (h * g))
        (Subsemiring.mem_center_iff.mp hz (single h 1))).symm
  · rintro ⟨hc, hi⟩
    apply Subsemiring.mem_center_iff.mpr
    have hmul : AddMonoidHom.mulRight z = AddMonoidHom.mulLeft z := by
      apply addMonoidHom_ext
      intro h r
      apply coeff_injective
      ext g
      have hshift : z.coeff (h⁻¹ * g) = z.coeff (g * h⁻¹) := by
        simpa [mul_assoc] using (hi h (h⁻¹ * g)).symm
      simpa [hshift] using
        (Subsemiring.mem_center_iff.mp (hc (g * h⁻¹)) r)
    intro x
    simpa using congrArg (fun f : R[G] →+ R[G] => f x) hmul

/-- Coefficients of a central group-algebra element are invariant under conjugation. -/
theorem coeff_conj_of_mem_center {z : R[G]} (hz : z ∈ Subsemiring.center (R[G]))
    (h g : G) : z.coeff (h * g * h⁻¹) = z.coeff g := by
  exact ((mem_center_iff z).mp hz).2 h g

/-- A nonzero coefficient of a central group-algebra element has a finite conjugation orbit.

For the commutative-ring class-sum description, compare the identity-twist case of Manju and
Sharma, Lemma 4.12 (see the module references). Here the conclusion follows from finite
coefficient support, without requiring commutative coefficients or additive inverses. -/
theorem finite_conjAct_orbit_of_coeff_ne_zero {z : R[G]}
    (hz : z ∈ Subsemiring.center (R[G])) {g : G} (hg : z.coeff g ≠ 0) :
    Set.Finite (MulAction.orbit (ConjAct G) g) := by
  refine z.coeff.support.finite_toSet.subset ?_
  intro k hk
  obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.mp hk
  apply Finsupp.mem_support_iff.mpr
  rw [ConjAct.smul_def, coeff_conj_of_mem_center hz]
  exact hg

/-- A central group-algebra element has zero coefficient on every infinite conjugation orbit.

Over commutative rings, compare the ordinary-center case of Manju and Sharma, Lemma 4.12
(see the module references). This finite-support consequence also holds for arbitrary semirings. -/
theorem coeff_eq_zero_of_not_finite_conjAct_orbit {z : R[G]}
    (hz : z ∈ Subsemiring.center (R[G])) {g : G}
    (hg : ¬ Set.Finite (MulAction.orbit (ConjAct G) g)) : z.coeff g = 0 := by
  by_contra hne
  exact hg (finite_conjAct_orbit_of_coeff_ne_zero hz hne)

/-- For a one-element group, centrality is centrality of the coefficient at the identity. -/
theorem mem_center_iff_of_subsingleton [Subsingleton G] (z : R[G]) :
    z ∈ Subsemiring.center (R[G]) ↔ z.coeff 1 ∈ Subsemiring.center R := by
  rw [mem_center_iff]
  constructor
  · intro hz
    exact hz.1 1
  · intro hz
    refine ⟨?_, ?_⟩
    · intro g
      simpa only [Subsingleton.elim g (1 : G)] using hz
    · intro h g
      exact congrArg (fun k : G => z.coeff k) (Subsingleton.elim _ _)

end Group

section CommSemiring

variable {R : Type u} {G : Type v} [CommSemiring R] [Group G]

/-- Over a commutative semiring, centrality is equivalent to conjugation invariance of
coefficients. -/
theorem mem_center_iff_coeff_conj (z : R[G]) :
    z ∈ Subsemiring.center (R[G]) ↔
      ∀ h g : G, z.coeff (h * g * h⁻¹) = z.coeff g := by
  simpa using (mem_center_iff z)

end CommSemiring

end MonoidAlgebra
