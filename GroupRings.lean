/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import GroupRings.MonoidAlgebra.AugmentationCrossedUniversal

public import GroupRings.MonoidAlgebra.AugmentationCrossedMaps

public import GroupRings.FreeAbelian.LaurentPolynomial
public import GroupRings.FiniteAbelian.RightConvolution
public import GroupRings.MonoidAlgebra.AugmentationNilpotence.Finite
public import GroupRings.MonoidAlgebra.FixedVectors
public import GroupRings.MonoidAlgebra.ModuleDetection
public import GroupRings.MonoidAlgebra.SimpleModules
public import GroupRings.MonoidAlgebra.ModuleRepresentation
public import GroupRings.MonoidAlgebra.ModuleRepresentationEquiv
public import GroupRings.MonoidAlgebra.SemisimpleModules
public import GroupRings.MonoidAlgebra.ModuleFiniteness
public import GroupRings.MonoidAlgebra.ModuleMaps
public import GroupRings.MonoidAlgebra.AugmentationBasis
public import GroupRings.MonoidAlgebra.AugmentationCotangent.Tensor
public import GroupRings.MonoidAlgebra.AugmentationCotangent.Functoriality
public import GroupRings.MonoidAlgebra.AugmentationGenerators
public import GroupRings.MonoidAlgebra.CoefficientChange
public import GroupRings.MonoidAlgebra.CoefficientIdeals
public import GroupRings.MonoidAlgebra.MixedQuotient
public import GroupRings.Polynomial.CoefficientIdeals
public import GroupRings.MonoidAlgebra.Units
public import GroupRings.MonoidAlgebra.SubgroupIdeals
public import GroupRings.MonoidAlgebra.SubgroupIdealsFG
public import GroupRings.MonoidAlgebra.SubgroupBasis
public import GroupRings.MonoidAlgebra.Quotient
public import GroupRings.MonoidAlgebra.KernelRange
public import GroupRings.MonoidAlgebra.Noetherian
public import GroupRings.MonoidAlgebra.MapDomain
public import GroupRings.RingTheory.Noetherian

/-!
# Monoid-algebra units, augmentation, Laurent coordinates and character convolution

The public entry point for the multivariable Laurent model, explicit-coordinate
algebra equivalence and canonical free-abelian specialization with basis laws,
as well as generic-field character bases, right convolution, diagonalization
and rank on finite abelian groups. Monoid-algebra augmentation is available over
any semiring, with its kernel generated as a left ideal by basis differences
over any ring. A monoid generating set, or a subgroup generating set for a
group, suffices for these left-ideal generators. The kernel also has a left
coefficient-ring module basis indexed by the nonidentity monoid elements.
For finite `p`-groups over any ring with prime `p = 0`, the augmentation
kernel has zero `Nat.card G`-th power, including over the zero ring.
Every nontrivial unital module of this algebra has a nonzero vector fixed by
all canonical group symbols. A module map is injective exactly when its map on
canonical fixed vectors is injective, and surjective exactly when its map on
augmentation coinvariants is surjective, without finite-generation assumptions.
A simple module has trivial group action on every vector, its action factors
through augmentation, and it is simple exactly when
its canonical coefficient restriction is simple. Noetherianity, Artinianity and
composition length in `ℕ∞` also agree with the canonical coefficient restriction
for every module. Semisimplicity is equivalent to coefficient semisimplicity
together with trivial canonical group action. The generic comparison allows any
scalar map surjective modulo a two-sided ideal whose action is uniformly nilpotent:
a module is semisimple exactly when the ideal annihilates it and its canonical
scalar restriction is semisimple. More generally, uniform
nilpotence of a left ideal action on a nontrivial semimodule yields a nonzero common annihilated
vector; two-sided ideals have a canonical common-annihilator submodule.
Over nontrivial rings with prime `p = 0`, uniform augmentation-ideal
nilpotence forces a common `p`-power exponent for an arbitrary group,
without finiteness or commutativity; for finite groups this gives an iff.
Vanishing of ideal powers over any semiring
is equivalent to vanishing of all ordered mixed products of the given length,
including zero.
Single-term units over a nontrivial semiring are characterized by unit
coefficients and unit monoid indices, without commutativity or
cancellation assumptions; coefficient-unit reflection needs no nontriviality.
Subgroup differences generate the left ideal of elements with zero coefficient
sums on left cosets, over any ring. Over a nontrivial ring these ideals detect
subgroup membership and order, and two-sidedness detects normality. The subgroup
left ideal is finitely generated whenever the subgroup is; over a nontrivial
ring the converse holds, including for the augmentation kernel and the whole group.
A left-Noetherian group algebra over a nontrivial ring has every subgroup finitely
generated. Surjective augmentation also allows left-Noetherianity to descend to
the coefficient semiring, using Mathlib's generic transport theorem.
Over every semiring, left-Noetherianity descends from a monoid algebra to the
algebra of any embedded group, hence to every subgroup algebra. Coefficient
projection supplies an additive right retraction, and a generic ideal
extension-contraction criterion transports the ascending chain condition.

For a group-to-monoid homomorphism, its group-ring pushforward has kernel the
left ideal of kernel-subgroup relations. The quotient is the monoid algebra of
the range submonoid, with unique factorization into any semiring target.
-/
