/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.Augmentation
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Artinian.Module

/-!
# Regular elements in monoid algebras

A single term is left-regular exactly when its coefficient is left-regular and
either the coefficient semiring is subsingleton or its index is left-regular.
The analogous statement holds on the right. The index type needs only a
multiplication; no global cancellation or nontriviality is required.
These criteria use Mathlib's finite-convolution coefficient-recovery and
single-term injectivity API.

For an infinite-order element of a cancellative monoid, a monic basis element minus
any constant is regular over an arbitrary coefficient ring. An annihilator would
have finite support containing an infinite orbit of multiplication by that element.
The two sides are treated separately, without commuting coefficients.

Consequently, a left Artinian monoid algebra with nontrivial coefficients has only
finite-order monoid elements: its right-regular elements are units, whereas
augmentation sends the difference of two coefficient-one basis elements to zero.
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

section Single

variable {R : Type u} {M : Type v} [Semiring R] [Mul M]

/-- A single term is left-regular exactly when its coefficient is left-regular and
its index is left-regular, unless the coefficient semiring is subsingleton. -/
theorem isLeftRegular_single_iff (m : M) (r : R) :
    IsLeftRegular (single m r : MonoidAlgebra R M) ↔
      IsLeftRegular r ∧ (Subsingleton R ∨ IsLeftRegular m) := by
  constructor
  · intro hs
    constructor
    · intro x y hxy
      apply single_right_injective (m := m)
      apply hs
      simpa only [single_mul_single] using congrArg (single (m * m)) hxy
    · rcases subsingleton_or_nontrivial R with hR | hR
      · exact Or.inl hR
      · let : Nontrivial R := hR
        right
        intro x y hxy
        apply single_left_injective (R := R) (r := 1) one_ne_zero
        apply hs
        simpa only [single_mul_single, mul_one] using
          congrArg (fun z : M => single z r) hxy
  · rintro ⟨hr, hR | hm⟩
    · let : Subsingleton R := hR
      intro f g _
      ext x
      exact Subsingleton.elim _ _
    · have hcoeff (f : MonoidAlgebra R M) (x : M) :
          (single m r * f).coeff (m * x) = r * f.coeff x :=
        coeff_single_mul_eq_mul_coeff x
          (fun y _ => ⟨fun h => hm h, fun h => congrArg (m * ·) h⟩)
      intro f g hfg
      ext x
      apply hr
      simpa only [hcoeff] using
        congrArg (fun a : MonoidAlgebra R M => a.coeff (m * x)) hfg

/-- A single term is right-regular exactly when its coefficient is right-regular and
its index is right-regular, unless the coefficient semiring is subsingleton. -/
theorem isRightRegular_single_iff (m : M) (r : R) :
    IsRightRegular (single m r : MonoidAlgebra R M) ↔
      IsRightRegular r ∧ (Subsingleton R ∨ IsRightRegular m) := by
  constructor
  · intro hs
    constructor
    · intro x y hxy
      apply single_right_injective (m := m)
      apply hs
      simpa only [single_mul_single] using congrArg (single (m * m)) hxy
    · rcases subsingleton_or_nontrivial R with hR | hR
      · exact Or.inl hR
      · let : Nontrivial R := hR
        right
        intro x y hxy
        apply single_left_injective (R := R) (r := 1) one_ne_zero
        apply hs
        simpa only [single_mul_single, one_mul] using
          congrArg (fun z : M => single z r) hxy
  · rintro ⟨hr, hR | hm⟩
    · let : Subsingleton R := hR
      intro f g _
      ext x
      exact Subsingleton.elim _ _
    · have hcoeff (f : MonoidAlgebra R M) (x : M) :
          (f * single m r).coeff (x * m) = f.coeff x * r :=
        coeff_mul_single_eq_coeff_mul x
          (fun y _ => ⟨fun h => hm h, fun h => congrArg (· * m) h⟩)
      intro f g hfg
      ext x
      apply hr
      simpa only [hcoeff] using
        congrArg (fun a : MonoidAlgebra R M => a.coeff (x * m)) hfg

end Single

variable {R : Type u} {M : Type v} [Ring R] [CancelMonoid M]

/-- A monic basis element at an infinite-order index minus any constant is regular.
Neither nontriviality nor commutativity of the coefficient ring is required. -/
theorem isRegular_single_sub_single {g : M} (hg : ¬IsOfFinOrder g) (r : R) :
    IsRegular (single g 1 - single 1 r : MonoidAlgebra R M) := by
  classical
  constructor
  · apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
    intro f hf
    have he : single g 1 * f = single 1 r * f :=
      sub_eq_zero.mp (by simpa only [sub_mul] using hf)
    have hs : f.coeff.support.image (g * ·) ⊆ f.coeff.support := by
      rw [← support_coeff_single_mul_eq_image f (r := 1) (by simp) (.all g), he]
      simpa only [one_mul, Finset.image_id'] using support_coeff_single_mul_subset f r 1
    apply MonoidAlgebra.ext
    ext m
    change f.coeff m = 0
    by_contra hm
    have horbit (n : ℕ) : g ^ n * m ∈ f.coeff.support := by
      induction n with
      | zero => simpa using Finsupp.mem_support_iff.mpr hm
      | succ n ih =>
        simpa only [pow_succ', mul_assoc] using
          hs (Finset.mem_image.mpr ⟨g ^ n * m, ih, rfl⟩)
    have hi : Function.Injective (fun n : ℕ ↦ g ^ n * m) := by
      intro n k hnk
      exact (injective_pow_iff_not_isOfFinOrder.mpr hg) (mul_right_cancel hnk)
    exact (Set.infinite_of_injective_forall_mem hi horbit) f.coeff.support.finite_toSet
  · apply isRightRegular_iff_left_eq_zero_of_mul.mpr
    intro f hf
    have he : f * single g 1 = f * single 1 r :=
      sub_eq_zero.mp (by simpa only [mul_sub] using hf)
    have hs : f.coeff.support.image (· * g) ⊆ f.coeff.support := by
      rw [← support_coeff_mul_single_eq_image f (r := 1) (by simp) (.all g), he]
      simpa only [mul_one, Finset.image_id'] using support_coeff_mul_single_subset f r 1
    apply MonoidAlgebra.ext
    ext m
    change f.coeff m = 0
    by_contra hm
    have horbit (n : ℕ) : m * g ^ n ∈ f.coeff.support := by
      induction n with
      | zero => simpa using Finsupp.mem_support_iff.mpr hm
      | succ n ih =>
        simpa only [pow_succ, mul_assoc] using
          hs (Finset.mem_image.mpr ⟨m * g ^ n, ih, rfl⟩)
    have hi : Function.Injective (fun n : ℕ ↦ m * g ^ n) := by
      intro n k hnk
      exact (injective_pow_iff_not_isOfFinOrder.mpr hg) (mul_left_cancel hnk)
    exact (Set.infinite_of_injective_forall_mem hi horbit) f.coeff.support.finite_toSet

/-- A left Artinian monoid algebra over a nontrivial ring has only finite-order
monoid elements. This does not assert that the monoid is finite. -/
theorem isOfFinOrder_of_isArtinianRing (R : Type u) {M : Type v} [Ring R]
    [CancelMonoid M] [Nontrivial R] [IsArtinianRing (MonoidAlgebra R M)] (g : M) :
    IsOfFinOrder g := by
  by_contra hg
  have hu := IsArtinianRing.isUnit_iff_isRightRegular.mpr
    (isRegular_single_sub_single (R := R) hg 1).right
  have hz : IsUnit (0 : R) := by
    simpa only [map_sub, augmentation_single, sub_self] using hu.map (augmentation R M)
  exact not_isUnit_zero hz

end MonoidAlgebra

/-- Left-regular coefficients and indices give left-regular single terms. -/
theorem IsLeftRegular.monoidAlgebra_single {R : Type u} {M : Type v}
    [Semiring R] [Mul M] {r : R} {m : M}
    (hr : IsLeftRegular r) (hm : IsLeftRegular m) :
    IsLeftRegular (MonoidAlgebra.single m r : MonoidAlgebra R M) :=
  (MonoidAlgebra.isLeftRegular_single_iff m r).mpr ⟨hr, Or.inr hm⟩

/-- Right-regular coefficients and indices give right-regular single terms. -/
theorem IsRightRegular.monoidAlgebra_single {R : Type u} {M : Type v}
    [Semiring R] [Mul M] {r : R} {m : M}
    (hr : IsRightRegular r) (hm : IsRightRegular m) :
    IsRightRegular (MonoidAlgebra.single m r : MonoidAlgebra R M) :=
  (MonoidAlgebra.isRightRegular_single_iff m r).mpr ⟨hr, Or.inr hm⟩

namespace AddMonoidAlgebra

variable {R : Type u} {M : Type v} [Ring R] [AddCancelMonoid M]

/-- The additive-index version of regularity of a monic basis element minus a constant. -/
theorem isRegular_single_sub_single {g : M} (hg : ¬IsOfFinAddOrder g) (r : R) :
    IsRegular (single g 1 - single 0 r : AddMonoidAlgebra R M) := by
  let : CancelMonoid (Multiplicative M) :=
    { (inferInstance : LeftCancelMonoid (Multiplicative M)),
      (inferInstance : RightCancelMonoid (Multiplicative M)) with }
  let e := toMultiplicative R M
  have hreg : IsRegular (e (single g 1 - single 0 r)) := by
    simpa only [e, map_sub, toMultiplicative_single, ofAdd_zero] using
      MonoidAlgebra.isRegular_single_sub_single (R := R)
        (g := Multiplicative.ofAdd g) (fun h ↦ hg (isOfFinOrder_ofAdd_iff.mp h)) r
  constructor
  · intro a b hab
    apply e.injective
    exact hreg.left (by simpa only [map_mul] using congrArg e hab)
  · intro a b hab
    apply e.injective
    exact hreg.right (by simpa only [map_mul] using congrArg e hab)

end AddMonoidAlgebra
