/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Noetherian modules over simple algebras

A compatible action of a simple algebra on a nontrivial module gives an
injective representation in the endomorphism algebra. If the module is
Noetherian over the commutative base ring, so is the algebra itself. In
particular, the algebra is finite over the base ring.

Consequently, an algebra that is not finite over the base ring has no
nontrivial compatible module that is Noetherian over the base ring. These
Noetherianity assertions concern modules over the base ring, not regular
modules over the simple algebra.
-/

@[expose] public section

namespace IsSimpleRing

universe u v w

variable (R : Type u) (A : Type v) (M : Type w)
variable [CommRing R] [Ring A] [Algebra R A] [IsSimpleRing A]
variable [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
variable [IsNoetherian R M]

/-- A simple algebra acting on a nontrivial module that is Noetherian over the
base ring is itself Noetherian over the base ring, and hence finite over it.
No Noetherianity assumption on the base ring is needed. -/
theorem isNoetherian_of_module [Nontrivial M] : IsNoetherian R A := by
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let ρ : A →ₐ[R] Module.End R M := Algebra.lsmul R R M
  exact isNoetherian_of_injective ρ.toLinearMap ρ.toRingHom.injective

/-- If a simple algebra is not finite over the base ring, every compatible
module that is Noetherian over the base ring is subsingleton. -/
theorem subsingleton_of_not_finite (hA : ¬ Module.Finite R A) : Subsingleton M := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · exact hM
  · let _ : Nontrivial M := hM
    let _ : IsNoetherian R A := isNoetherian_of_module R A M
    exact (hA inferInstance).elim

end IsSimpleRing
