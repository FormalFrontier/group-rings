/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Characters and right convolution on a finite abelian group

Over a field containing enough roots of unity, additive characters form a basis of the
space of functions on a finite abelian group. Right convolution with kernel `f` has
entries `f (-sigma + tau)`; its eigenvalue at `psi` is `∑ x, f x * psi x`.

The generic-field development adapts a finite-abelian character experiment by
Beacon (commit `4457d01b7397a1b431bdf0e566f11202227de187`). The original
incubator implementation was authored by Hive Task
`hive-request-463616387133379beaef446d80cf547b5f475217`, UID
`6baba0b3-2702-448c-99b0-87925b4466b1`; its public-module packaging was
repaired by worker-b Hive Task `hive-request-485dac1da11e46e88fdd51d0c7df9b3e246fdcdb`,
UID `183381ed-5f4a-45d7-a4e9-f6cf0a1889be`. This delivery adapts that API
under the project's pinned mathlib dependency.
-/

@[expose] public section

open Function Module Multiplicative
open scoped Matrix

noncomputable section

universe u v
variable {G : Type u} {K : Type v} [AddCommGroup G] [Field K]

namespace AddChar

/-- Dedekind independence for field-valued additive characters, with no finiteness hypothesis. -/
theorem linearIndependent_field : LinearIndependent K ((⇑) : AddChar G K → G → K) := by
  have independent : LinearIndependent K
      (fun psi : AddChar G K => (psi.toMonoidHom : Multiplicative G → K)) :=
    (linearIndependent_monoidHom (Multiplicative G) K).comp
      AddChar.toMonoidHom (fun _ _ equality => AddChar.toMonoidHomEquiv.injective equality)
  let transport : (Multiplicative G → K) ≃ₗ[K] (G → K) :=
    LinearEquiv.piCongrLeft K (fun _ : G => K) Multiplicative.toAdd
  have transported := independent.map' transport.toLinearMap transport.ker
  have evaluation : (fun psi : AddChar G K => transport psi.toMonoidHom) =
      ((⇑) : AddChar G K → G → K) := by
    funext psi g
    rfl
  change LinearIndependent K (fun psi : AddChar G K => transport psi.toMonoidHom) at transported
  rwa [evaluation] at transported

/-- A finite group has only finitely many characters valued in a field. -/
theorem finite_of_field [Finite G] : Finite (AddChar G K) := by
  let : Fintype G := Fintype.ofFinite G
  exact (linearIndependent_field (G := G) (K := K)).finite

variable [Finite G] [HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative G))]

/-- The dual of a finite abelian group has the same cardinality when the field has enough roots. -/
theorem natCard_eq_of_hasEnoughRootsOfUnity : Nat.card (AddChar G K) = Nat.card G := by
  rw [Nat.card_congr AddChar.toMonoidHomMulEquiv.toEquiv,
    Nat.card_congr MonoidHom.toHomUnitsMulEquiv.toEquiv,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]
  exact Nat.card_congr Multiplicative.toAdd

/-- Evaluation of characters gives a basis of all field-valued functions on a finite
abelian group, provided the field has sufficiently many roots of unity. -/
def basisOfEnoughRootsOfUnity : Basis (AddChar G K) K (G → K) := by
  let : Fintype G := Fintype.ofFinite G
  let : Finite (AddChar G K) := finite_of_field (G := G) (K := K)
  let : Fintype (AddChar G K) := Fintype.ofFinite (AddChar G K)
  apply basisOfLinearIndependentOfCardEqFinrank linearIndependent_field
  rw [Module.finrank_fintype_fun_eq_card]
  simpa only [Nat.card_eq_fintype_card] using
    (natCard_eq_of_hasEnoughRootsOfUnity (G := G) (K := K))

@[simp]
theorem coe_basisOfEnoughRootsOfUnity :
    ⇑(basisOfEnoughRootsOfUnity (G := G) (K := K)) =
      ((⇑) : AddChar G K → G → K) := by
  let : Fintype G := Fintype.ofFinite G
  let : Finite (AddChar G K) := finite_of_field (G := G) (K := K)
  let : Fintype (AddChar G K) := Fintype.ofFinite (AddChar G K)
  rw [basisOfEnoughRootsOfUnity, coe_basisOfLinearIndependentOfCardEqFinrank]

@[simp]
theorem basisOfEnoughRootsOfUnity_apply (psi : AddChar G K) :
    basisOfEnoughRootsOfUnity (G := G) (K := K) psi = (psi : G → K) :=
  congrFun (coe_basisOfEnoughRootsOfUnity (G := G) (K := K)) psi

end AddChar

namespace FiniteFourier

variable [Fintype G]

/-- Matrix of right convolution, with row `sigma` and column `tau` entry
`f (-sigma + tau)`. -/
def rightConvolution (f : G → K) : Matrix G G K := fun sigma tau => f (-sigma + tau)

/-- Positive-character Fourier coefficient of a right-convolution kernel. -/
def rightConvolutionEigenvalue (f : G → K) (psi : AddChar G K) : K :=
  ∑ x : G, f x * psi x

/-- Each character is an eigenvector for right convolution, without requiring
the field to contain enough roots of unity for a complete character basis. -/
theorem rightConvolution_mulVec_addChar (f : G → K) (psi : AddChar G K) :
    rightConvolution f *ᵥ (psi : G → K) =
      rightConvolutionEigenvalue f psi • (psi : G → K) := by
  ext sigma
  simp only [rightConvolution, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
    rightConvolutionEigenvalue]
  calc
    (∑ tau : G, f (-sigma + tau) * psi tau) =
        ∑ x : G, f x * psi (sigma + x) := by
      refine Fintype.sum_equiv (Equiv.addLeft (-sigma)) _ _ ?_
      intro tau
      simp
    _ = (∑ x : G, f x * psi x) * psi sigma := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [psi.map_add_eq_mul]
      ring

variable [HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative G))]

/-- Right convolution is diagonal in the character basis. The basis-index
`Fintype` and `DecidableEq` instances are explicit public parameters, and can
be provided locally using `AddChar.finite_of_field` and `Fintype.ofFinite`. -/
theorem toMatrix_rightConvolution [Fintype (AddChar G K)] [DecidableEq (AddChar G K)]
    (f : G → K) :
    LinearMap.toMatrix (AddChar.basisOfEnoughRootsOfUnity (G := G) (K := K))
        (AddChar.basisOfEnoughRootsOfUnity (G := G) (K := K))
        (rightConvolution f).mulVecLin =
      Matrix.diagonal (rightConvolutionEigenvalue f) := by
  classical
  ext psi chi
  rw [LinearMap.toMatrix_apply, AddChar.basisOfEnoughRootsOfUnity_apply,
    Matrix.mulVecLin_apply, rightConvolution_mulVec_addChar, map_smul]
  have representation :
      (AddChar.basisOfEnoughRootsOfUnity (G := G) (K := K)).repr (chi : G → K) =
        Finsupp.single chi 1 := by
    rw [← AddChar.basisOfEnoughRootsOfUnity_apply]
    exact (AddChar.basisOfEnoughRootsOfUnity (G := G) (K := K)).repr_self chi
  rw [representation]
  by_cases equal : psi = chi
  · subst psi
    simp
  · simp [equal]

/-- The rank of right convolution is the number of characters with nonzero
positive-character Fourier coefficient. No character-index `Fintype` is
required in the public statement. -/
theorem rank_rightConvolution (f : G → K) : (rightConvolution f).rank =
    Nat.card {psi : AddChar G K // rightConvolutionEigenvalue f psi ≠ 0} := by
  classical
  let : Finite (AddChar G K) := AddChar.finite_of_field (G := G) (K := K)
  let : Fintype (AddChar G K) := Fintype.ofFinite (AddChar G K)
  let basis : Basis (AddChar G K) K (G → K) :=
    AddChar.basisOfEnoughRootsOfUnity (G := G) (K := K)
  calc
    (rightConvolution f).rank = Module.finrank K
        (LinearMap.range (rightConvolution f).mulVecLin) := rfl
    _ = (LinearMap.toMatrix basis basis (rightConvolution f).mulVecLin).rank := by
      symm
      have equality := Matrix.rank_eq_finrank_range_toLin
        (LinearMap.toMatrix basis basis (rightConvolution f).mulVecLin) basis basis
      rw [Matrix.toLin_toMatrix] at equality
      exact equality
    _ = (Matrix.diagonal (rightConvolutionEigenvalue f)).rank := by
      exact congrArg Matrix.rank (toMatrix_rightConvolution (G := G) (K := K) f)
    _ = Nat.card {psi : AddChar G K // rightConvolutionEigenvalue f psi ≠ 0} := by
      rw [Matrix.rank_diagonal, Nat.card_eq_fintype_card]

end FiniteFourier
