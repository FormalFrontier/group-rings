/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Coordinates on a pointed coefficient-sum kernel

For an `S`-module `V` with additive inverses and a point `b : T`, restriction away
from `b` identifies the kernel of the coefficient sum with `{t : T // t ≠ b} →₀ V`.
The inverse extends by zero and subtracts the sum at `b`.

The sum map is Mathlib's `Finsupp.lsum ℕ (fun _ => LinearMap.id)`. Here `ℕ` is
its auxiliary scalar parameter; the resulting map is `S`-linear, without a
commuting action of `S` on itself. The scalar, coefficient and index universes
are independent.

## Implementation notes

The construction uses Mathlib's linear restriction and extension maps
`Finsupp.lsubtypeDomain` and `Finsupp.lmapDomain`, and its finitely supported sum
laws. No ring structure on `S` or operation on `T` is required.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Finsupp

variable (S : Type u) (V : Type v) {T : Type w}
variable [Semiring S] [AddCommGroup V] [Module S V]

private theorem sum_zero_ext (b : T) (x y : T →₀ V)
    (hx : x.sum (fun _ v => v) = 0) (hy : y.sum (fun _ v => v) = 0)
    (h : ∀ t, t ≠ b → x t = y t) : x = y := by
  have hd : x - y = single b (x b - y b) := by
    ext t
    by_cases ht : t = b
    · simp [ht]
    · simp [ht, h t ht]
  have hs := congrArg (fun f : T →₀ V => f.sum (fun _ v => v)) hd
  have hb : x b - y b = 0 := by
    simpa [sum_sub_index, hx, hy] using hs.symm
  exact sub_eq_zero.mp (by rw [hd, hb, single_zero])

/-- Restriction away from `b` gives coordinates on the kernel of the `S`-linear
coefficient sum. Its inverse extends the coordinates by zero and subtracts their
sum at `b`. -/
def kerLsumEquiv (b : T) :
    LinearMap.ker (lsum ℕ (fun _ : T => (LinearMap.id : V →ₗ[S] V))) ≃ₗ[S]
      ({t : T // t ≠ b} →₀ V) where
  toFun x := lsubtypeDomain (R := S) {t : T | t ≠ b} (x : T →₀ V)
  invFun g := ⟨lmapDomain V S Subtype.val g -
    lsingle (R := S) b
      (lsum ℕ (fun _ : {t : T // t ≠ b} => (LinearMap.id : V →ₗ[S] V)) g), by
      change (lsum ℕ (fun _ : T => (LinearMap.id : V →ₗ[S] V))) _ = 0
      simp [lsum_apply, sum_sub_index, sum_mapDomain_index, Function.id_def]⟩
  left_inv x := by
    apply Subtype.ext
    apply sum_zero_ext V b
    · simp [lsum_apply, sum_sub_index, sum_mapDomain_index, Function.id_def]
    · exact x.property
    · intro t ht
      simp [lsubtypeDomain_apply, ht,
        mapDomain_apply_of_injective Subtype.val_injective _ (⟨t, ht⟩ : {t // t ≠ b})]
  right_inv g := by
    ext t
    have ht : (t : T) ≠ b := t.property
    simp [lsubtypeDomain_apply, ht,
      mapDomain_apply_of_injective Subtype.val_injective g t]
  map_add' x y :=
    (lsubtypeDomain (R := S) (M := V) {t : T | t ≠ b}).map_add
      (x : T →₀ V) (y : T →₀ V)
  map_smul' r x :=
    (lsubtypeDomain (R := S) (M := V) {t : T | t ≠ b}).map_smul r (x : T →₀ V)

/-- The forward map is restriction to the off-point subtype. -/
theorem kerLsumEquiv_apply (b : T)
    (x : LinearMap.ker (lsum ℕ (fun _ : T => (LinearMap.id : V →ₗ[S] V)))) :
    kerLsumEquiv S V b x = subtypeDomain (fun t => t ≠ b) (x : T →₀ V) := rfl

/-- Each forward coordinate is the original coefficient at that index. -/
@[simp]
theorem kerLsumEquiv_apply_apply (b : T)
    (x : LinearMap.ker (lsum ℕ (fun _ : T => (LinearMap.id : V →ₗ[S] V))))
    (t : {t : T // t ≠ b}) :
    kerLsumEquiv S V b x t = (x : T →₀ V) t := rfl

/-- The inverse is extension along subtype inclusion minus the single
correction at the distinguished point. -/
theorem kerLsumEquiv_symm_apply_coe (b : T) (g : {t : T // t ≠ b} →₀ V) :
    ((kerLsumEquiv S V b).symm g : T →₀ V) =
      mapDomain Subtype.val g - single b (g.sum (fun _ v => v)) := rfl

/-- Away from the distinguished point the inverse preserves every coordinate. -/
@[simp]
theorem kerLsumEquiv_symm_apply_apply (b : T) (g : {t : T // t ≠ b} →₀ V)
    (t : {t : T // t ≠ b}) :
    ((kerLsumEquiv S V b).symm g : T →₀ V) t = g t := by
  simp [kerLsumEquiv_symm_apply_coe, t.property,
    mapDomain_apply_of_injective Subtype.val_injective g t]

/-- At the distinguished point the inverse has the negative sum of the coordinates. -/
@[simp]
theorem kerLsumEquiv_symm_apply_same (b : T) (g : {t : T // t ≠ b} →₀ V) :
    ((kerLsumEquiv S V b).symm g : T →₀ V) b = -g.sum (fun _ v => v) := by
  rw [kerLsumEquiv_symm_apply_coe, sub_apply, single_eq_same,
    mapDomain_of_notMem_range]
  · exact zero_sub _
  · rintro ⟨t, ht⟩
    exact t.property ht

end Finsupp
