/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.CoefficientIdeals
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomial transport of coefficient ideals

The composite of `Polynomial.toFinsuppIso R` and
`AddMonoidAlgebra.toMultiplicative R ℕ` identifies polynomials with the monoid
algebra on `Multiplicative ℕ`. This module gives constant, coefficient and
coefficient-change compatibility, and transports extended ideals and kernels.

In particular the monoid-algebra coefficient-ideal theorem specializes to
Mathlib's `Ideal.mem_map_C_iff` for every commutative coefficient semiring,
ideal and polynomial. The kernel transport specializes to
`Polynomial.ker_mapRingHom` for every commutative coefficient semiring and
independently universed semiring target. The transport itself works already
for noncommutative semiring coefficients; it is not a new polynomial model.

## References

The equivalences and polynomial operations are Mathlib's. The ideal and kernel
transport relate the general monoid-algebra theorem to Mathlib's
`Mathlib.RingTheory.Polynomial.Basic` results, preserving their full parameters.
-/

@[expose] public section

universe u v

namespace Polynomial

variable {R : Type u} {S : Type v} [Semiring R] [Semiring S]

/-- Polynomial constants are the constants of the multiplicative-index monoid algebra. -/
theorem toMultiplicative_toFinsuppIso_C (r : R) :
    (AddMonoidAlgebra.toMultiplicative R ℕ) (toFinsuppIso R (C r)) =
      MonoidAlgebra.single 1 r := by
  simp

/-- The coefficient at `ofAdd n` is precisely the original polynomial coefficient at `n`. -/
theorem coeff_toMultiplicative_toFinsuppIso (p : R[X]) (n : ℕ) :
    ((AddMonoidAlgebra.toMultiplicative R ℕ) (toFinsuppIso R p)).coeff
      (Multiplicative.ofAdd n) = p.coeff n := by
  simp [AddMonoidAlgebra.toMultiplicative, toFinsupp_apply]

/-- The polynomial transport commutes with arbitrary coefficient change. -/
theorem toMultiplicative_toFinsuppIso_map (f : R →+* S) (p : R[X]) :
    (AddMonoidAlgebra.toMultiplicative S ℕ) (toFinsuppIso S (Polynomial.mapRingHom f p)) =
      MonoidAlgebra.mapRingHom (Multiplicative ℕ) f
        ((AddMonoidAlgebra.toMultiplicative R ℕ) (toFinsuppIso R p)) := by
  ext m
  obtain ⟨n, rfl⟩ := Multiplicative.ofAdd.surjective m
  simp [toFinsupp_apply]

/-- Transport of polynomial ideal extension is extension by monoid-algebra constants. -/
theorem map_C_toMultiplicative_toFinsuppIso (I : Ideal R) :
    Ideal.map ((toFinsuppIso R).trans (AddMonoidAlgebra.toMultiplicative R ℕ)).toRingHom
        (Ideal.map C I) =
      Ideal.map (MonoidAlgebra.singleOneRingHom (M := Multiplicative ℕ)) I := by
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro r
  exact toMultiplicative_toFinsuppIso_C r

/-- Membership transport for every coefficient ideal and every polynomial.
Together with `MonoidAlgebra.mem_map_singleOneRingHom_iff` and the coefficient
formula, this recovers `Ideal.mem_map_C_iff` with all its original parameters. -/
theorem mem_map_C_toMultiplicative_toFinsuppIso_iff (I : Ideal R) (p : R[X]) :
    (AddMonoidAlgebra.toMultiplicative R ℕ) (toFinsuppIso R p) ∈
        Ideal.map (MonoidAlgebra.singleOneRingHom (M := Multiplicative ℕ)) I ↔
      p ∈ Ideal.map C I := by
  rw [← map_C_toMultiplicative_toFinsuppIso]
  exact Ideal.apply_mem_of_equiv_iff
    (f := (toFinsuppIso R).trans (AddMonoidAlgebra.toMultiplicative R ℕ))

/-- Polynomial coefficient kernels transport to monoid-algebra coefficient kernels;
the target coefficient semiring has an independent universe. -/
theorem map_ker_toMultiplicative_toFinsuppIso (f : R →+* S) :
    Ideal.map ((toFinsuppIso R).trans (AddMonoidAlgebra.toMultiplicative R ℕ)).toRingHom
        (RingHom.ker (Polynomial.mapRingHom f)) =
      RingHom.ker (MonoidAlgebra.mapRingHom (Multiplicative ℕ) f) := by
  ext x
  obtain ⟨p, rfl⟩ :=
    ((toFinsuppIso R).trans (AddMonoidAlgebra.toMultiplicative R ℕ)).surjective x
  have hmem :
      ((toFinsuppIso R).trans (AddMonoidAlgebra.toMultiplicative R ℕ)) p ∈
          Ideal.map ((toFinsuppIso R).trans (AddMonoidAlgebra.toMultiplicative R ℕ)).toRingHom
            (RingHom.ker (Polynomial.mapRingHom f)) ↔
        p ∈ RingHom.ker (Polynomial.mapRingHom f) :=
    Ideal.apply_mem_of_equiv_iff
      (f := (toFinsuppIso R).trans (AddMonoidAlgebra.toMultiplicative R ℕ))
  rw [hmem, RingHom.mem_ker, RingHom.mem_ker]
  change Polynomial.mapRingHom f p = 0 ↔
    MonoidAlgebra.mapRingHom (Multiplicative ℕ) f
      ((AddMonoidAlgebra.toMultiplicative R ℕ) (toFinsuppIso R p)) = 0
  rw [← toMultiplicative_toFinsuppIso_map]
  exact (map_eq_zero_iff
    ((toFinsuppIso S).trans (AddMonoidAlgebra.toMultiplicative S ℕ))
    ((toFinsuppIso S).trans (AddMonoidAlgebra.toMultiplicative S ℕ)).injective).symm

/-- Transported polynomial kernels equal transported extension of the coefficient
kernel. In commutative source coefficients this is exactly the transport of
`Polynomial.ker_mapRingHom`, without fixing either coefficient universe or `f`. -/
theorem map_ker_eq_map_C_toMultiplicative_toFinsuppIso (f : R →+* S) :
    Ideal.map ((toFinsuppIso R).trans (AddMonoidAlgebra.toMultiplicative R ℕ)).toRingHom
        (RingHom.ker (Polynomial.mapRingHom f)) =
      Ideal.map ((toFinsuppIso R).trans (AddMonoidAlgebra.toMultiplicative R ℕ)).toRingHom
        (Ideal.map C (RingHom.ker f)) := by
  rw [map_ker_toMultiplicative_toFinsuppIso, MonoidAlgebra.ker_mapRingHom,
    map_C_toMultiplicative_toFinsuppIso]

end Polynomial
