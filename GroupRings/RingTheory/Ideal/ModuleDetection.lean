/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Ideal.ModuleDetection
public import GroupRings.RingTheory.Ideal.Annihilator

/-!
# Detection of module maps by nilpotent ideals

Restriction to the common annihilator of a nilpotent two-sided ideal detects
injectivity of linear maps between additive groups. Reduction modulo a nilpotent
left ideal detects surjectivity, without any finite-generation hypothesis.
The latter follows by applying uniform nilpotence to the cokernel.

The common-annihilator map is a restriction of the given map. The quotient map
is Mathlib's `Submodule.mapQ`, on the quotients by `I • ⊤`.

The declarations are re-exported from `CoherentModules.RingTheory.Ideal.ModuleDetection`.
-/
