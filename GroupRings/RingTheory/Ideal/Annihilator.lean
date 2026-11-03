/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Ideal.Annihilator
public import GroupRings.RingTheory.Ideal.Powers

/-!
# Common annihilators of ideals

If one power of a left ideal annihilates a nontrivial semimodule, some nonzero
vector is annihilated by the whole ideal. This is uniform nilpotence of the
action: the ideal itself need not be nilpotent. The proof reduces the length of
ordered words, and needs neither right ideal closure nor additive inverses.

For a two-sided ideal, the common-annihilator carrier is a submodule. Its
universal property pairs it with the scalar-valued `Submodule.annihilator`.
Over commutative semirings it agrees with Mathlib's `Submodule.torsionBySet`.

The declarations are re-exported from `CoherentModules.RingTheory.Ideal.Annihilator`.
-/
