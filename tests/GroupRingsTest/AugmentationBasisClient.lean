/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Left coefficient coordinates over a matrix ring

The augmentation-kernel basis over `Matrix (Fin 2) (Fin 2) ℤ` and the nongroup
monoid `Multiplicative ℕ` detects the order of coefficient multiplication.
The coordinate of `E₀₁ • (E₁₀ • b)` is `E₀₁E₁₀`, whose `(0,0)` entry is one;
the reversed product has entry zero. Both the vector and coordinate laws are
used through the public import.
-/

noncomputable section

example :
    let R := Matrix (Fin 2) (Fin 2) ℤ
    let a : R := !![0, 1; 0, 0]
    let c : R := !![0, 0; 1, 0]
    let t : {m : Multiplicative ℕ // m ≠ 1} :=
      ⟨Multiplicative.ofAdd 1, Nat.one_ne_zero⟩
    let B := MonoidAlgebra.augmentationKerBasis R (Multiplicative ℕ)
    (B.repr (a • (c • B t)) t) 0 0 = 1 ∧ (c * a) 0 0 = 0 := by
  dsimp only
  rw [MonoidAlgebra.augmentationKerBasis_repr_apply]
  simp [MonoidAlgebra.coeff_smul, MonoidAlgebra.one_def, Matrix.mul_apply,
    Fin.sum_univ_two]
