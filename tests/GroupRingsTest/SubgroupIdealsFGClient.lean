/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite generation through the public subgroup-ideal API

Over the noncommutative ring `M₂(ℤ)`, the infinite cyclic group gives a finitely
generated subgroup left ideal and augmentation kernel, with a nonzero difference.
The zero ring is allowed in the forward theorem. In contrast, for the
infinite-rank free abelian group, the augmentation kernel is finitely generated
over the zero ring but not over the integers: coefficient nontriviality is
necessary for the converse.
-/

noncomputable section

open MonoidAlgebra

private theorem matrix_cyclic_ideals :
    (Ideal.span (Set.range (fun h : (⊤ : Subgroup (Multiplicative ℤ)) =>
      single (h : Multiplicative ℤ) (1 : Matrix (Fin 2) (Fin 2) ℤ) - 1)) :
      Ideal (MonoidAlgebra (Matrix (Fin 2) (Fin 2) ℤ) (Multiplicative ℤ))).FG ∧
    (RingHom.ker (augmentation (Matrix (Fin 2) (Fin 2) ℤ) (Multiplicative ℤ))).FG ∧
    single (Multiplicative.ofAdd (1 : ℤ)) (1 : Matrix (Fin 2) (Fin 2) ℤ) - 1 ≠
      (0 : MonoidAlgebra (Matrix (Fin 2) (Fin 2) ℤ) (Multiplicative ℤ)) := by
  refine ⟨span_subgroup_fg_of_fg _ ⊤ Group.FG.out, ker_augmentation_fg _ _, ?_⟩
  intro h
  have hc := congrArg (fun f : MonoidAlgebra (Matrix (Fin 2) (Fin 2) ℤ)
    (Multiplicative ℤ) => f.coeff (Multiplicative.ofAdd (1 : ℤ))) h
  simp [MonoidAlgebra.one_def] at hc

private theorem infinite_rank_not_fg : ¬ Group.FG (Multiplicative (ℕ →₀ ℤ)) := by
  intro h
  have hAdd : AddGroup.FG (ℕ →₀ ℤ) := AddGroup.fg_iff_mul_fg.mpr h
  have hFin : Module.Finite ℤ (ℕ →₀ ℤ) := Module.Finite.iff_addGroup_fg.mpr hAdd
  exact Module.not_finite_of_infinite_basis
    (Finsupp.basisSingleOne : Module.Basis ℕ ℤ (ℕ →₀ ℤ)) hFin

private theorem coefficient_boundary :
    (RingHom.ker (augmentation (ZMod 1) (Multiplicative ℤ))).FG ∧
    (RingHom.ker (augmentation (ZMod 1) (Multiplicative (ℕ →₀ ℤ)))).FG ∧
    ¬ (RingHom.ker (augmentation ℤ (Multiplicative (ℕ →₀ ℤ)))).FG := by
  refine ⟨ker_augmentation_fg _ _, ?_, ?_⟩
  · have hbot : RingHom.ker (augmentation (ZMod 1) (Multiplicative (ℕ →₀ ℤ))) = ⊥ :=
      Subsingleton.elim _ _
    rw [hbot]
    exact Submodule.fg_bot
  · exact fun h => infinite_rank_not_fg ((ker_augmentation_fg_iff ℤ _).mp h)
