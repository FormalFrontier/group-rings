/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings

/-! Ordinary-import examples for generic-field character bases and right convolution. -/

open Multiplicative
open scoped Matrix

noncomputable section

universe u v
variable {G : Type u} {K : Type v} [AddCommGroup G] [Field K]

section Basis

variable [Finite G] [HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative G))]

private theorem test_basis_apply (psi : AddChar G K) :
    AddChar.basisOfEnoughRootsOfUnity (G := G) (K := K) psi = (psi : G → K) := by
  exact AddChar.basisOfEnoughRootsOfUnity_apply psi

end Basis

section Convolution

variable [Fintype G]

private theorem test_eigenvector (f : G → K) (psi : AddChar G K) :
    FiniteFourier.rightConvolution f *ᵥ (psi : G → K) =
      FiniteFourier.rightConvolutionEigenvalue f psi • (psi : G → K) := by
  exact FiniteFourier.rightConvolution_mulVec_addChar f psi

variable [HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative G))]

private theorem test_rank (f : G → K) :
    (FiniteFourier.rightConvolution f).rank =
      Nat.card {psi : AddChar G K // FiniteFourier.rightConvolutionEigenvalue f psi ≠ 0} :=
  FiniteFourier.rank_rightConvolution f

private theorem test_diagonalization (f : G → K) :
    letI : Finite (AddChar G K) := AddChar.finite_of_field (G := G) (K := K)
    letI : Fintype (AddChar G K) := Fintype.ofFinite (AddChar G K)
    LinearMap.toMatrix (AddChar.basisOfEnoughRootsOfUnity (G := G) (K := K))
        (AddChar.basisOfEnoughRootsOfUnity (G := G) (K := K))
        (FiniteFourier.rightConvolution f).mulVecLin =
      Matrix.diagonal (FiniteFourier.rightConvolutionEigenvalue f) := by
  classical
  let : Finite (AddChar G K) := AddChar.finite_of_field (G := G) (K := K)
  let : Fintype (AddChar G K) := Fintype.ofFinite (AddChar G K)
  exact FiniteFourier.toMatrix_rightConvolution f

end Convolution

section Sign

variable [Fintype G] [DecidableEq G]

private theorem test_positive_sign (a : G) (psi : AddChar G K) :
    FiniteFourier.rightConvolutionEigenvalue (fun x => if x = a then 1 else 0) psi =
      psi a := by
  simp [FiniteFourier.rightConvolutionEigenvalue]

end Sign

section ComplexComparison

variable [Finite G] [HasEnoughRootsOfUnity ℂ (Monoid.exponent (Multiplicative G))]

private theorem test_complex_comparison :
    AddChar.basisOfEnoughRootsOfUnity (G := G) (K := ℂ) =
    AddChar.complexBasis G := by
  apply DFunLike.ext
  intro psi
  simp

end ComplexComparison
