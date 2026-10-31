/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings.MonoidAlgebra.CyclicNoetherian
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Cyclic Noetherianity with noncommutative and zero coefficients

The finite-product example uses matrix multiplication on the coefficient
ring and a finite group factor. The second example retains the zero ring.
-/

example : IsNoetherianRing
    (MonoidAlgebra (Matrix (Fin 2) (Fin 2) ℚ)
      (Multiplicative ℤ × Multiplicative (ZMod 2))) := by
  let : IsNoetherianRing (Matrix (Fin 2) (Fin 2) ℚ) :=
    isNoetherian_of_tower ℚ
      (inferInstance : IsNoetherian ℚ (Matrix (Fin 2) (Fin 2) ℚ))
  exact MonoidAlgebra.isNoetherianRing_multiplicative_int_prod_iff.mpr inferInstance

example : IsNoetherianRing (MonoidAlgebra (ZMod 1) (Multiplicative ℤ)) :=
  MonoidAlgebra.isNoetherianRing_multiplicative_int_iff.mpr inferInstance
