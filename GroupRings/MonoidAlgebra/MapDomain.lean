/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Coefficient projection along a group embedding

Mathlib's `MonoidAlgebra.comapDomain` is an additive retraction of the
unchanged-coefficient pushforward along an injection. When the source is a
group and the target is any monoid, this projection commutes with right
multiplication by the image of the source algebra.

The projection need not be a ring homomorphism. The proof uses only that the
image of every source-group element is a unit; no cancellation in the target
monoid or freeness over the source algebra is required. Coefficients retain
their original order, so noncommutative semirings are allowed.
-/

@[expose] public section

universe u v w

namespace MonoidAlgebra

variable {R : Type u} {H : Type v} {M : Type w} [Semiring R]

/-- Coefficient pullback retracts unchanged-coefficient pushforward along an
injection. This bridges the monoid-algebra representation to the Finsupp law. -/
@[simp]
theorem comapDomain_mapDomain (j : H → M) (hj : Function.Injective j)
    (b : MonoidAlgebra R H) : comapDomain j hj (mapDomain j b) = b := by
  apply coeff_injective
  exact Finsupp.comapDomain_mapDomain j hj b.coeff

/-- Pulling back coefficients along a group embedding commutes with right
multiplication by the image. The coefficient factors retain their original order. -/
theorem comapDomain_mul_mapDomain [Group H] [Monoid M]
    (j : H →* M) (hj : Function.Injective j) (a : MonoidAlgebra R M)
    (b : MonoidAlgebra R H) :
    comapDomain j hj (a * mapDomainRingHom R j b) = comapDomain j hj a * b := by
  induction b using induction_linear with
  | zero => simp
  | add b c hb hc =>
    simp only [map_add, mul_add, comapDomain_add, hb, hc]
  | single h r =>
    change comapDomain j hj (a * mapDomain j (single h r)) = _
    rw [mapDomain_single]
    ext k
    simp only [coeff_comapDomain, Finsupp.comapDomain_apply, coeff_mul_single_apply]
    apply coeff_mul_single_eq_coeff_mul
    intro m _
    constructor
    · intro hm
      calc
        m = m * (j h * j (h⁻¹)) := by rw [← map_mul, mul_inv_cancel, map_one, mul_one]
        _ = (m * j h) * j (h⁻¹) := (mul_assoc ..).symm
        _ = j k * j (h⁻¹) := by rw [hm]
        _ = j (k * h⁻¹) := (map_mul ..).symm
    · rintro rfl
      rw [← map_mul, inv_mul_cancel_right]

end MonoidAlgebra
