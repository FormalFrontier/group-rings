/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.RingTheory.Noetherian
public import Mathlib.RingTheory.Artinian.Defs

/-!
# Left Artinianity and additive right retractions

Let `f : A →+* B` have an additive retraction `E : B →+ A` satisfying
`E (b * f a) = E b * a`. Then left Artinianity of `B` implies left
Artinianity of `A`. The retraction need not preserve multiplication or be
left-linear. The semirings may be noncommutative or zero.

Under the right-multiplication compatibility, the retraction condition
`∀ a, E (f a) = a` is equivalent to `E 1 = 1`: evaluate the compatibility
at `b = 1` for one direction, and evaluate the retraction at `a = 1` for
the other.

## Implementation notes

Extension of ordinary left ideals reflects inclusion by
`RingHom.ideal_map_le_iff_of_additive_retraction`. The resulting order
embedding transfers well-foundedness of strict inclusion. This does not
assert that `B` is Artinian as an `A`-module, nor that a left Artinian
semiring is right Artinian.
-/

@[expose] public section

universe u v

namespace RingHom

variable {A : Type u} {B : Type v} [Semiring A] [Semiring B]

/-- Left Artinianity descends along a semiring homomorphism with an additive
retraction compatible with right multiplication by its image. -/
theorem isArtinianRing_of_additive_retraction
    (f : A →+* B) (E : B →+ A)
    (hE : ∀ a, E (f a) = a)
    (hmul : ∀ b a, E (b * f a) = E b * a)
    [IsArtinianRing B] : IsArtinianRing A := by
  let e : Ideal A ↪o Ideal B := OrderEmbedding.ofMapLEIff (Ideal.map f)
    (f.ideal_map_le_iff_of_additive_retraction E hE hmul)
  exact e.wellFoundedLT

end RingHom
