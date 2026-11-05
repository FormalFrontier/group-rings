/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.Units
public import GroupRings.MonoidAlgebra.SupportUniqueProds
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# Units in monoid algebras with two unique products

Over a semiring without zero divisors, units in the convolution algebra of a
monoid with two unique products are precisely single terms with a unit index
and a unit coefficient. The additive-index statement uses additive units for
the index, while coefficients and algebra units remain multiplicative.
Neither statement requires nontrivial coefficients.

The statements use Mathlib's `TwoUniqueProds` and `TwoUniqueSums` classes and
canonical monoid-algebra structures, together with the single-term unit API in
`GroupRings.MonoidAlgebra.Units`.

For the classical group case, the passage from unique products to two unique
products is due to Andrzej Strojnowski, as credited in Mathlib's unique-product
development. The statements here use a two-unique-product monoid and a
no-zero-divisor semiring; this broader semiring/monoid form is not attributed
to Strojnowski's group theorem.

## References

* Andrzej Strojnowski, *A note on u.p. groups* (1980), for the classical
  unique-product group ingredient.
* Mathlib's `Algebra.Group.UniqueProds.Basic` for that ingredient's formalization,
  and `Algebra.MonoidAlgebra.NoZeroDivisors` and `Algebra.MonoidAlgebra.Support`
  for the convolution coefficient and support APIs.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped Pointwise

namespace MonoidAlgebra

/-- A convolution unit over a no-zero-divisor semiring and a monoid with two
unique products is exactly a single term with unit index and unit coefficient.

For the classical unique-product group ingredient, see Andrzej Strojnowski,
*A note on u.p. groups* (1980), and the module references. The stated
coefficient and index scope extends that group setting. -/
theorem isUnit_iff_exists_single_units {R : Type u} {M : Type v}
    [Semiring R] [NoZeroDivisors R] [Monoid M] [TwoUniqueProds M]
    (f : MonoidAlgebra R M) :
    IsUnit f ↔ ∃ (m : Units M) (r : Units R),
      f = MonoidAlgebra.single m.val r.val := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · let : Subsingleton R := hR
    have hsingle : f = single (1 : M) (1 : R) := by
      apply MonoidAlgebra.ext
      exact Finsupp.ext fun _ => Subsingleton.elim _ _
    constructor
    · intro _
      exact ⟨1, 1, hsingle⟩
    · intro _
      have hone : f = 1 := by
        apply MonoidAlgebra.ext
        exact Finsupp.ext fun _ => Subsingleton.elim _ _
      rw [hone]
      exact isUnit_one
  · let : Nontrivial R := hR
    have hcard_one : (1 : MonoidAlgebra R M).coeff.support.card ≤ 1 := by
      calc
        _ ≤ (1 : Finset M).card := Finset.card_le_card support_coeff_one_subset
        _ = 1 := Finset.card_one
    constructor
    · intro hf
      obtain ⟨g, hfg, hgf⟩ := isUnit_iff_exists.mp hf
      have hg : g.coeff ≠ 0 := by
        intro hg
        have hgzero : g = 0 := MonoidAlgebra.ext (hg.trans coeff_zero.symm)
        have honezero : (1 : MonoidAlgebra R M) = 0 := by
          rw [hgzero, mul_zero] at hfg
          exact hfg.symm
        have hnonempty : (1 : MonoidAlgebra R M).coeff.support.Nonempty := by
          rw [support_coeff_one]
          exact Finset.one_nonempty
        rw [honezero, coeff_zero, Finsupp.support_zero] at hnonempty
        exact Finset.not_nonempty_empty hnonempty
      have hcard_g : 1 ≤ g.coeff.support.card :=
        Finset.one_le_card.mpr (Finsupp.support_nonempty_iff.mpr hg)
      have hcard_f : f.coeff.support.card ≤ 1 := by
        apply not_lt.mp
        intro hcard
        have hmul := one_lt_card_support_coeff_mul f g
          (one_lt_mul_of_lt_of_le hcard hcard_g)
        rw [hfg] at hmul
        exact (not_lt.mpr hcard_one) hmul
      obtain ⟨m, r, hsingle⟩ := Finsupp.card_support_le_one'.mp hcard_f
      have hsingle' : f = single m r :=
        MonoidAlgebra.ext (hsingle.trans (coeff_single m r).symm)
      have hunit : IsUnit r ∧ IsUnit m :=
        (isUnit_single_iff m r).mp (hsingle' ▸ hf)
      obtain ⟨ru, hr⟩ := hunit.1
      obtain ⟨mu, hm⟩ := hunit.2
      exact ⟨mu, ru, by simpa only [hr, hm] using hsingle'⟩
    · rintro ⟨m, r, rfl⟩
      exact (isUnit_single_iff m.val r.val).mpr ⟨r.isUnit, m.isUnit⟩

end MonoidAlgebra

namespace AddMonoidAlgebra

/-- A convolution unit over a no-zero-divisor semiring and an additive monoid
with two unique sums is exactly a single term with additive-unit index and
multiplicative-unit coefficient.

For the classical unique-product group ingredient, see Andrzej Strojnowski,
*A note on u.p. groups* (1980), and the module references. This is the
additive-index semiring/monoid form, not a statement attributed to that paper. -/
theorem isUnit_iff_exists_single_units {R : Type u} {A : Type v}
    [Semiring R] [NoZeroDivisors R] [AddMonoid A] [TwoUniqueSums A]
    (f : AddMonoidAlgebra R A) :
    IsUnit f ↔ ∃ (a : AddUnits A) (r : Units R),
      f = AddMonoidAlgebra.single a.val r.val := by
  let e := toMultiplicative R A
  constructor
  · intro hf
    obtain ⟨m, r, hm⟩ := (MonoidAlgebra.isUnit_iff_exists_single_units (e f)).mp
      ((MulEquiv.isUnit_map e.toMulEquiv).mpr hf)
    let a : AddUnits A :=
      { val := m.val.toAdd
        neg := m.inv.toAdd
        val_neg := by
          simpa only [toAdd_mul, toAdd_one] using
            congrArg Multiplicative.toAdd m.val_inv
        neg_val := by
          simpa only [toAdd_mul, toAdd_one] using
            congrArg Multiplicative.toAdd m.inv_val }
    have hval : Multiplicative.ofAdd a.val = m.val := ofAdd_toAdd m.val
    refine ⟨a, r, e.injective ?_⟩
    calc
      e f = MonoidAlgebra.single m.val r.val := hm
      _ = e (single a.val r.val) := by
        simp only [e, toMultiplicative_single, hval]
  · rintro ⟨a, r, rfl⟩
    let m : Units (Multiplicative A) :=
      { val := Multiplicative.ofAdd a.val
        inv := Multiplicative.ofAdd a.neg
        val_inv := by
          simpa only [ofAdd_add, ofAdd_zero] using
            congrArg Multiplicative.ofAdd a.val_neg
        inv_val := by
          simpa only [ofAdd_add, ofAdd_zero] using
            congrArg Multiplicative.ofAdd a.neg_val }
    apply (MulEquiv.isUnit_map e.toMulEquiv).mp
    apply (MonoidAlgebra.isUnit_iff_exists_single_units _).mpr
    exact ⟨m, r, toMultiplicative_single a.val r.val⟩

end AddMonoidAlgebra
