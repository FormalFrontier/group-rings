/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.RingTheory.Congruence.Coatomic
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Simple quotients by ring congruences

A quotient of a possibly nonassociative unital ring is simple exactly when its defining
congruence is a coatom in the congruence lattice. The proof transports the lattice of
two-sided ideals of the quotient through the congruence correspondence.

The characterization needs no nontriviality assumption on the ring or its quotient.
In particular, the top congruence has a trivial quotient, and neither simplicity nor the
coatom condition holds. Coatomicity then gives a nonzero simple quotient of every
nontrivial unital ring, without associativity, commutativity or chain conditions.
-/

@[expose] public section

namespace RingCon

/-- The quotient by a ring congruence is simple if and only if the congruence is a coatom.
Simplicity includes nontriviality, so this also excludes the top congruence without a
separate nontriviality hypothesis on the quotient. -/
theorem isSimpleRing_quotient_iff_isCoatom {R : Type*} [NonAssocRing R] (c : RingCon R) :
    IsSimpleRing c.Quotient ↔ IsCoatom c := by
  rw [isSimpleRing_iff]
  exact (TwoSidedIdeal.orderIsoRingCon (R := c.Quotient)).isSimpleOrder_iff.trans
    ((RingCon.correspondence (c := c)).isSimpleOrder_iff.symm.trans
      Set.isSimpleOrder_Ici_iff_isCoatom)

/-- Every nontrivial unital ring has a nonzero simple quotient by a ring congruence.
The quotient is the canonical `c.Quotient`, with surjective map `c.mk'`; its nontriviality
follows from `IsSimpleRing.instNontrivial`. Multiplication need not be associative. -/
theorem exists_isSimpleRing_quotient {R : Type*} [NonAssocRing R] [Nontrivial R] :
    ∃ c : RingCon R, IsSimpleRing c.Quotient := by
  obtain ⟨c, hc⟩ := IsCoatomic.exists_coatom (α := RingCon R)
  exact ⟨c, (isSimpleRing_quotient_iff_isCoatom c).mpr hc⟩

end RingCon
