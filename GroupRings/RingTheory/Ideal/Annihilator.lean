/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.RingTheory.Ideal.Powers
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Common annihilators of ideals

If one power of a left ideal annihilates a nontrivial semimodule, some nonzero
vector is annihilated by the whole ideal. This is uniform nilpotence of the
action: the ideal itself need not be nilpotent. The proof reduces the length of
ordered words, and needs neither right ideal closure nor additive inverses.

For a two-sided ideal, the common-annihilator carrier is a submodule. Its
universal property pairs it with the scalar-valued `Submodule.annihilator`.
Over commutative semirings it agrees with Mathlib's `Submodule.torsionBySet`.
-/

@[expose] public section

universe u w

namespace Ideal

variable {A : Type u} [Semiring A]
variable {V : Type w} [AddCommMonoid V] [Module A V]

/-- A uniformly nilpotent ideal action on a nontrivial semimodule has a nonzero
common annihilated vector. The ideal is an ordinary left ideal, and the exponent
may be zero. -/
theorem exists_ne_zero_le_torsionOf_of_pow_le_annihilator [Nontrivial V]
    (I : Ideal A) {n : ℕ} (hI : I ^ n ≤ Module.annihilator A V) :
    ∃ x : V, x ≠ 0 ∧ I ≤ torsionOf A V x := by
  classical
  by_contra! h
  have common_zero (x : V) (hx : I ≤ torsionOf A V x) : x = 0 := by
    by_contra hx0
    exact h x hx0 hx
  -- If the common kernel is zero, reducing word length detects every vector.
  have word_zero : ∀ k : ℕ, ∀ x : V,
      (∀ l : List A, l.length = k → (∀ a ∈ l, a ∈ I) → l.prod • x = 0) → x = 0 := by
    intro k
    induction k with
    | zero =>
      intro x hx
      simpa using hx [] rfl (by simp)
    | succ k ih =>
      intro x hx
      apply common_zero
      intro a ha
      apply (mem_torsionOf_iff x a).mpr
      apply ih (a • x)
      intro l hl hmem
      have hword := hx (l ++ [a]) (by simp [hl]) (by
        intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact hmem b hb
        · rcases List.mem_singleton.mp hb with rfl
          exact ha)
      simpa only [List.prod_append, List.prod_singleton, mul_smul] using hword
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  apply hx
  apply word_zero n x
  intro l hl hmem
  exact Module.mem_annihilator.mp
    ((pow_le_iff_forall_list_prod_mem n).mp hI l hl hmem) x

/-- A nilpotent left ideal has a nonzero common annihilated vector in every
nontrivial semimodule. -/
theorem exists_ne_zero_le_torsionOf_of_isNilpotent [Nontrivial V]
    (I : Ideal A) (hI : IsNilpotent I) :
    ∃ x : V, x ≠ 0 ∧ I ≤ torsionOf A V x := by
  obtain ⟨n, hn⟩ := hI
  apply exists_ne_zero_le_torsionOf_of_pow_le_annihilator I (n := n)
  rw [hn]
  exact bot_le

variable (V)

/-- The submodule of vectors annihilated by every element of a two-sided ideal.
Two-sidedness ensures closure under the scalar action even when scalars do not
commute. -/
def annihilatorSubmodule (I : Ideal A) [I.IsTwoSided] : Submodule A V where
  carrier := {x | I ≤ torsionOf A V x}
  zero_mem' := by simp
  add_mem' hx hy a ha := by
    rw [mem_torsionOf_iff, smul_add,
      (mem_torsionOf_iff _ _).mp (hx ha), (mem_torsionOf_iff _ _).mp (hy ha), zero_add]
  smul_mem' r x hx a ha := by
    rw [mem_torsionOf_iff, ← mul_smul]
    exact (mem_torsionOf_iff _ _).mp (hx (I.mul_mem_right r ha))

variable {V} {I J : Ideal A}

/-- Membership in the common-annihilator submodule means that every scalar in
the ideal annihilates the vector. -/
@[simp]
theorem mem_annihilatorSubmodule_iff [I.IsTwoSided] {x : V} :
    x ∈ annihilatorSubmodule V I ↔ ∀ a ∈ I, a • x = 0 := Iff.rfl

/-- Enlarging the ideal shrinks its common-annihilator submodule. -/
theorem annihilatorSubmodule_anti [I.IsTwoSided] [J.IsTwoSided] (h : I ≤ J) :
    annihilatorSubmodule V J ≤ annihilatorSubmodule V I :=
  fun _ hx _ ha => hx (h ha)

/-- Every vector is annihilated by the zero ideal. -/
@[simp]
theorem annihilatorSubmodule_bot : annihilatorSubmodule V (⊥ : Ideal A) = ⊤ := by
  ext x
  simp

/-- Only the zero vector is annihilated by every scalar. -/
@[simp]
theorem annihilatorSubmodule_top : annihilatorSubmodule V (⊤ : Ideal A) = ⊥ := by
  ext x
  simp only [mem_annihilatorSubmodule_iff, Submodule.mem_bot]
  constructor
  · intro h
    simpa only [one_smul] using h 1 (Submodule.mem_top)
  · rintro rfl
    exact fun a _ => smul_zero a

/-- The common-annihilator submodule is the largest submodule annihilated by
the ideal. -/
theorem le_annihilatorSubmodule_iff [I.IsTwoSided] {N : Submodule A V} :
    N ≤ annihilatorSubmodule V I ↔ I ≤ N.annihilator := by
  constructor
  · intro h a ha
    exact Submodule.mem_annihilator.mpr fun x hx =>
      (mem_annihilatorSubmodule_iff.mp (h hx)) a ha
  · intro h x hx
    exact mem_annihilatorSubmodule_iff.mpr fun a ha =>
      Submodule.mem_annihilator.mp (h ha) x hx

/-- Ideal multiplication annihilates a submodule exactly when that submodule
lies in the common annihilator. -/
theorem le_annihilatorSubmodule_iff_smul_eq_bot [I.IsTwoSided] {N : Submodule A V} :
    N ≤ annihilatorSubmodule V I ↔ I • N = ⊥ :=
  le_annihilatorSubmodule_iff.trans Submodule.le_annihilator_iff

/-- Uniformly nilpotent action makes the common-annihilator submodule nonzero. -/
theorem annihilatorSubmodule_ne_bot_of_pow_le_annihilator [Nontrivial V]
    [I.IsTwoSided] {n : ℕ} (hI : I ^ n ≤ Module.annihilator A V) :
    annihilatorSubmodule V I ≠ ⊥ := by
  obtain ⟨x, hx, hmem⟩ := exists_ne_zero_le_torsionOf_of_pow_le_annihilator I hI
  intro hbot
  exact hx (by simpa only [Submodule.mem_bot] using
    (show x ∈ (⊥ : Submodule A V) from hbot ▸ hmem))

section CommSemiring

variable {B : Type u} [CommSemiring B] {W : Type w} [AddCommMonoid W] [Module B W]

/-- For commutative scalars, the ideal common annihilator agrees with the
set-torsion submodule. -/
theorem annihilatorSubmodule_eq_torsionBySet (I : Ideal B) :
    annihilatorSubmodule W I = Submodule.torsionBySet B W (I : Set B) := by
  ext x
  simp only [mem_annihilatorSubmodule_iff, Submodule.mem_torsionBySet_iff,
    Subtype.forall, SetLike.mem_coe]

end CommSemiring

end Ideal
