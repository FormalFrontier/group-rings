/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Data.Matrix.Basis

/-!
# Finite matrices and monoid algebras

Monoid algebras commute with finite square matrix semirings. The equivalence
`MonoidAlgebra.matrixRingEquiv` preserves each matrix entry of every monoid
coefficient. It uses ordinary matrix multiplication and monoid convolution,
without commutativity assumptions on either the coefficients or the monoid.

The construction uses Mathlib's finitely supported coefficient maps and matrix
units. Its inverse has finite support because the matrix has finitely many entries.
-/

@[expose] public noncomputable section

universe uR uM un

namespace MonoidAlgebra

variable {R : Type uR} {M : Type uM} {n : Type un}
variable [Semiring R] [Monoid M] [Fintype n] [DecidableEq n]

/-- The canonical ring equivalence between a monoid algebra of finite square
matrices and finite square matrices of monoid-algebra entries. Each matrix entry
of every monoid coefficient is unchanged. Empty matrix indices and the zero
coefficient semiring are allowed. -/
def matrixRingEquiv : MonoidAlgebra (Matrix n n R) M ≃+*
    Matrix n n (MonoidAlgebra R M) := by
  -- Evaluate every coefficient matrix at one entry.
  let matrixTo : MonoidAlgebra (Matrix n n R) M → Matrix n n (MonoidAlgebra R M) :=
    fun f i j => ofCoeff (f.coeff.mapRange (fun A => A i j) rfl)
  have matrixTo_coeff (f : MonoidAlgebra (Matrix n n R) M) (i j : n) (m : M) :
      ((matrixTo f) i j).coeff m = (f.coeff m) i j := by
    dsimp only [matrixTo]
    rw [coeff_ofCoeff]
    exact Finsupp.mapRange_apply
  -- A finite sum of matrix units assembles the inverse coefficients.
  let matrixFrom : Matrix n n (MonoidAlgebra R M) → MonoidAlgebra (Matrix n n R) M :=
    fun X => ofCoeff (∑ i, ∑ j,
      (X i j).coeff.mapRange (Matrix.single i j) (Matrix.single_zero i j))
  have matrixFrom_coeff (X : Matrix n n (MonoidAlgebra R M)) (m : M) (i j : n) :
      ((matrixFrom X).coeff m) i j = (X i j).coeff m := by
    simp [matrixFrom, Matrix.sum_sum_single]
  -- The two coefficient formulas give the additive equivalence.
  let matrixAddEquiv : MonoidAlgebra (Matrix n n R) M ≃+
      Matrix n n (MonoidAlgebra R M) := {
    toFun := matrixTo
    invFun := matrixFrom
    left_inv f := by
      apply coeff_injective
      apply Finsupp.ext
      intro m
      funext i j
      rw [matrixFrom_coeff, matrixTo_coeff]
    right_inv X := by
      funext i j
      apply coeff_injective
      apply Finsupp.ext
      intro m
      rw [matrixTo_coeff, matrixFrom_coeff]
    map_add' f g := by
      funext i j
      apply coeff_injective
      apply Finsupp.ext
      intro m
      simp [matrixTo_coeff] }
  have matrixAddEquiv_single (m : M) (A : Matrix n n R) (i j : n) :
      (matrixAddEquiv (single m A)) i j = single m (A i j) := by
    apply coeff_injective
    apply Finsupp.ext
    intro a
    rw [show ((matrixAddEquiv (single m A)) i j).coeff a =
      ((single m A).coeff a) i j from matrixTo_coeff _ _ _ _]
    by_cases h : m = a <;> simp [h]
  -- Matrix multiplication and convolution agree on single terms.
  have matrixAddEquiv_mul_single (a b : M) (A B : Matrix n n R) :
      matrixAddEquiv (single a A * single b B) =
        matrixAddEquiv (single a A) * matrixAddEquiv (single b B) := by
    funext i j
    let S : R →+ MonoidAlgebra R M :=
      { toFun := single (a * b)
        map_zero' := by simp
        map_add' := by intros; simp }
    have hS : single (a * b) (∑ k, A i k * B k j) =
        ∑ k, single (a * b) (A i k * B k j) := by
      change S (∑ k, A i k * B k j) = ∑ k, S (A i k * B k j)
      simp
    simpa [matrixAddEquiv_single, Matrix.mul_apply] using hS
  -- Additive extensionality in each factor extends the single-term calculation.
  have matrixAddEquiv_mul (f g : MonoidAlgebra (Matrix n n R) M) :
      matrixAddEquiv (f * g) = matrixAddEquiv f * matrixAddEquiv g := by
    let e : MonoidAlgebra (Matrix n n R) M ≃+ Matrix n n (MonoidAlgebra R M) := matrixAddEquiv
    have hsingle (a : M) (A : Matrix n n R) (y : MonoidAlgebra (Matrix n n R) M) :
        e (single a A * y) = e (single a A) * e y := by
      let lhs : MonoidAlgebra (Matrix n n R) M →+ Matrix n n (MonoidAlgebra R M) :=
        { toFun := fun y => e (single a A * y)
          map_zero' := by simp
          map_add' := by intros; simp [mul_add] }
      let rhs : MonoidAlgebra (Matrix n n R) M →+ Matrix n n (MonoidAlgebra R M) :=
        { toFun := fun y => e (single a A) * e y
          map_zero' := by simp
          map_add' := by intros; simp [mul_add] }
      have h : lhs = rhs := addMonoidHom_ext fun b B => matrixAddEquiv_mul_single a b A B
      exact congrArg (fun k : MonoidAlgebra (Matrix n n R) M →+
        Matrix n n (MonoidAlgebra R M) => k y) h
    let lhs : MonoidAlgebra (Matrix n n R) M →+ Matrix n n (MonoidAlgebra R M) :=
      { toFun := fun x => e (x * g)
        map_zero' := by simp
        map_add' := by intros; simp [add_mul] }
    let rhs : MonoidAlgebra (Matrix n n R) M →+ Matrix n n (MonoidAlgebra R M) :=
      { toFun := fun x => e x * e g
        map_zero' := by simp
        map_add' := by intros; simp [add_mul] }
    have h : lhs = rhs := addMonoidHom_ext fun a A => hsingle a A g
    exact congrArg (fun k : MonoidAlgebra (Matrix n n R) M →+
      Matrix n n (MonoidAlgebra R M) => k f) h
  exact { matrixAddEquiv with map_mul' := matrixAddEquiv_mul }

/-- A coefficient of an entry of `matrixRingEquiv` is the corresponding entry
of the original coefficient matrix. -/
@[simp]
theorem matrixRingEquiv_coeff (f : MonoidAlgebra (Matrix n n R) M) (i j : n) (m : M) :
    ((matrixRingEquiv f) i j).coeff m = (f.coeff m) i j := by
  change (ofCoeff (f.coeff.mapRange (fun A => A i j) rfl)).coeff m = (f.coeff m) i j
  rw [coeff_ofCoeff]
  exact Finsupp.mapRange_apply (hf := rfl)

/-- The inverse equivalence forms a coefficient matrix from the coefficients
of the individual entries. -/
@[simp]
theorem matrixRingEquiv_symm_coeff (X : Matrix n n (MonoidAlgebra R M)) (m : M) (i j : n) :
    ((matrixRingEquiv.symm X).coeff m) i j = (X i j).coeff m := by
  change (ofCoeff (∑ k, ∑ l,
    (X k l).coeff.mapRange (Matrix.single k l) (Matrix.single_zero k l))).coeff m i j = _
  simp [Matrix.sum_sum_single]

/-- A single monoid term is sent entrywise to the single with the same index. -/
@[simp]
theorem matrixRingEquiv_single (m : M) (A : Matrix n n R) (i j : n) :
    (matrixRingEquiv (single m A)) i j = single m (A i j) := by
  apply coeff_injective
  apply Finsupp.ext
  intro a
  rw [matrixRingEquiv_coeff]
  by_cases h : m = a <;> simp [h]

/-- A matrix of singles at a common monoid index is sent back to one single
whose coefficient is the matrix of their coefficients. -/
@[simp]
theorem matrixRingEquiv_symm_single (m : M) (A : Matrix n n R) :
    matrixRingEquiv.symm (fun i j => single m (A i j)) = single m A := by
  apply coeff_injective
  apply Finsupp.ext
  intro a
  funext i j
  calc
    ((matrixRingEquiv.symm (fun k l : n => single m (A k l))).coeff a) i j =
        (single m (A i j)).coeff a := matrixRingEquiv_symm_coeff _ _ _ _
    _ = (single m A).coeff a i j := by
      by_cases h : m = a <;> simp [h]

/-- The equivalence interchanges a monoid single and a matrix unit. -/
@[simp]
theorem matrixRingEquiv_single_single (m : M) (i j : n) (r : R) :
    matrixRingEquiv (single m (Matrix.single i j r)) =
      Matrix.single i j (single m r) := by
  funext k l
  rw [matrixRingEquiv_single]
  by_cases h : i = k ∧ j = l <;> simp [h]

/-- The inverse equivalence interchanges a matrix unit and a monoid single. -/
@[simp]
theorem matrixRingEquiv_symm_single_single (m : M) (i j : n) (r : R) :
    matrixRingEquiv.symm (Matrix.single i j (single m r)) =
      single m (Matrix.single i j r) := by
  apply coeff_injective
  apply Finsupp.ext
  intro a
  funext k l
  rw [matrixRingEquiv_symm_coeff]
  by_cases h : m = a <;> by_cases h' : i = k ∧ j = l <;> simp [h, h']

/-- Multiplication of adjacent matrix units after transport preserves both the
monoid order and the coefficient order. -/
theorem matrixRingEquiv_single_single_mul (a b : M) (i j k : n) (r s : R) :
    matrixRingEquiv
        (single a (Matrix.single i j r) * single b (Matrix.single j k s)) =
      Matrix.single i k (single (a * b) (r * s)) := by
  rw [map_mul, matrixRingEquiv_single_single, matrixRingEquiv_single_single,
    Matrix.single_mul_single_same]
  simp

end MonoidAlgebra
