/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Congruence.Basic

/-!
# Coatomicity of ring congruences

The greatest ring congruence is compact: in a nonempty directed supremum, the relation
between `0` and `1` already holds in one member, and that member is the greatest
congruence. Consequently, every proper ring congruence lies below a coatom.

The results apply to unital nonassociative semirings, including the zero semiring.
In fact, only an addition and a multiplication with an absorbing zero and an identity
are needed; no distributivity or associativity assumptions are used.
-/

@[expose] public section

namespace RingCon

variable {R : Type*}

private theorem exists_rel_of_sSup_rel [Add R] [Mul R]
    (s : Set (RingCon R)) (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    {x y : R} (hxy : (sSup s) x y) : ∃ c ∈ s, c x y := by
  let u : RingCon R :=
    { r := fun x y => ∃ c ∈ s, c x y
      iseqv := by
        refine ⟨?_, ?_, ?_⟩
        · intro x
          obtain ⟨c, hc⟩ := hs
          exact ⟨c, hc, c.refl x⟩
        · rintro x y ⟨c, hc, h⟩
          exact ⟨c, hc, c.symm h⟩
        · rintro x y z ⟨c, hc, hxy⟩ ⟨d, hd, hyz⟩
          obtain ⟨e, he, hce, hde⟩ := hdir c hc d hd
          exact ⟨e, he, e.trans (hce hxy) (hde hyz)⟩
      add' := by
        rintro w x y z ⟨c, hc, hwx⟩ ⟨d, hd, hyz⟩
        obtain ⟨e, he, hce, hde⟩ := hdir c hc d hd
        exact ⟨e, he, e.add (hce hwx) (hde hyz)⟩
      mul' := by
        rintro w x y z ⟨c, hc, hwx⟩ ⟨d, hd, hyz⟩
        obtain ⟨e, he, hce, hde⟩ := hdir c hc d hd
        exact ⟨e, he, e.mul (hce hwx) (hde hyz)⟩ }
  have hu : sSup s ≤ u := sSup_le fun c hc _ _ h => ⟨c, hc, h⟩
  exact hu hxy

variable [Add R] [MulZeroOneClass R]

/-- The greatest ring congruence is compact when multiplication has an absorbing zero
and an identity. -/
theorem isCompactElement_top : IsCompactElement (⊤ : RingCon R) := by
  rw [isCompactElement_iff_le_of_directed_sSup_le]
  intro s hs hdir htop
  have h01 : (sSup s) (0 : R) 1 := htop trivial
  obtain ⟨c, hc, hc01⟩ := exists_rel_of_sSup_rel s hs hdir h01
  refine ⟨c, hc, ?_⟩
  intro x y _
  have hx : c 0 x := by
    simpa only [zero_mul, one_mul] using c.mul hc01 (c.refl x)
  have hy : c 0 y := by
    simpa only [zero_mul, one_mul] using c.mul hc01 (c.refl y)
  exact c.trans (c.symm hx) hy

/-- Ring congruences form a coatomic lattice when multiplication has an absorbing zero
and an identity. -/
instance : IsCoatomic (RingCon R) :=
  CompleteLattice.coatomic_of_top_compact isCompactElement_top

end RingCon
