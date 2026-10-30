# Common annihilators and finite p-group fixed vectors

```lean
import GroupRings
```

The common-annihilator theory is in
[`GroupRings.RingTheory.Ideal.Annihilator`](../GroupRings/RingTheory/Ideal/Annihilator.lean).
Its application to canonical monoid-algebra actions is in
[`GroupRings.MonoidAlgebra.FixedVectors`](../GroupRings/MonoidAlgebra/FixedVectors.lean).

## Uniform nilpotence of an action

Let `A` be any semiring, `V` any nontrivial unital `A`-semimodule, and `I` an
ordinary left ideal. If

```lean
hI : I ^ n ≤ Module.annihilator A V
```

then `Ideal.exists_ne_zero_le_torsionOf_of_pow_le_annihilator I hI` gives

```lean
∃ x : V, x ≠ 0 ∧ I ≤ Ideal.torsionOf A V x
```

The hypothesis says that every ordered product of `n` elements of `I` kills
every vector of `V`. There is **one uniform exponent**, not a separate exponent
for each scalar or vector. It need not make `I ^ n` zero in `A`. For example,
`(2)^2` annihilates the natural `ℤ`-module `ℤ/4ℤ`, although `(2)` is not a
nilpotent ideal of `ℤ`. The class of 2 is a nonzero common annihilated vector;
the action of 2 on the class of 1 is nonzero.

No two-sidedness, subtraction, additive cancellation, finite generation or
finiteness is required. The scalar and vector universes are independent. Degree
zero is allowed: its hypothesis would force the whole module to be trivial.
The corollary `Ideal.exists_ne_zero_le_torsionOf_of_isNilpotent I hI` assumes
`IsNilpotent I` instead, and follows by containment in the module annihilator.

The proof uses ordered words. If the common kernel were zero, induction on word
length would show that a vector killed by every word of any fixed length is
zero. To reduce the length, apply the inductive hypothesis to `a • x` and
append `a` to each word. This works for ordinary left ideals over semirings.

## The common-annihilator submodule

For a two-sided ideal,

```lean
Ideal.annihilatorSubmodule V I : Submodule A V
```

has carrier exactly `{x | I ≤ Ideal.torsionOf A V x}`. Use
`Ideal.mem_annihilatorSubmodule_iff` to express membership as
`∀ a ∈ I, a • x = 0`. Right closure of `I` is used only to prove scalar closure:
`a • (r • x) = (a * r) • x`. Scalar multiplication by an individual `a` need
not be an `A`-linear map when `A` is noncommutative.

The characteristic API includes:

- `annihilatorSubmodule_anti`: enlarging the ideal shrinks its common annihilator;
- simp laws `annihilatorSubmodule_bot` and `annihilatorSubmodule_top`;
- `le_annihilatorSubmodule_iff`:
  `N ≤ Ideal.annihilatorSubmodule V I ↔ I ≤ N.annihilator`;
- `le_annihilatorSubmodule_iff_smul_eq_bot`:
  the same containment is equivalent to `I • N = ⊥`, using Mathlib's scalar
  annihilator API;
- `annihilatorSubmodule_ne_bot_of_pow_le_annihilator` for uniformly nilpotent
  actions on nontrivial modules;
- `annihilatorSubmodule_eq_torsionBySet`, identifying this submodule with
  `Submodule.torsionBySet A V (I : Set A)` over a commutative semiring.

`Module.annihilator` and `Submodule.annihilator` are scalar ideals; this
construction instead consists of vectors. It introduces no additional action
or representation model.

## Augmentation and canonical fixed vectors

For a ring `R`, monoid `M`, and any unital `R[M]`-module `V`,
`MonoidAlgebra.ker_augmentation_le_torsionOf_iff x` gives

```lean
RingHom.ker (MonoidAlgebra.augmentation R M) ≤
    Ideal.torsionOf (MonoidAlgebra R M) V x ↔
  ∀ m : M, MonoidAlgebra.single m (1 : R) • x = x
```

This works for any vector, including zero and vectors of trivial modules.
There is no group, characteristic or finiteness assumption. The proof uses the
left-ideal generators `single m 1 - 1` of the kernel. Additive inverses are
induced internally from the ring-module structure; the public assumption on
`V` remains `AddCommMonoid V`.

The simp theorem `mem_annihilatorSubmodule_ker_augmentation_iff` identifies the
kernel's common-annihilator submodule with these fixed vectors. These are the
fixed vectors for the given module's canonical action, obtained by composing
its scalar action with `MonoidAlgebra.of R M`; no unrelated monoid action is
chosen.

For a finite group `G`, prime `p`, `(p : R) = 0` and `IsPGroup p G`,
`MonoidAlgebra.annihilatorSubmodule_ker_augmentation_ne_bot_of_isPGroup`
shows that this submodule is nonzero. It uses the augmentation bound
`augmentation_pow_card_eq_bot`. Consequently,

```lean
MonoidAlgebra.exists_ne_zero_fixed_of_isPGroup hp hR hG
```

gives a nonzero vector fixed by every `single g 1` in every nontrivial unital
`R[G]`-module. The coefficient ring may be noncommutative. No field, coefficient
commutativity, `CharP`, finite-dimensionality, finite generation or finite
underlying module is assumed. `R`, `G` and `V` have independent universes.
The statement also allows zero coefficient rings, but such rings have no
nontrivial unital modules, so it does not assert an impossible example there.

The [public-import client](../tests/GroupRingsTest/FixedVectorsClient.lean)
uses action nilpotence on `ℤ/4ℤ` and obtains a fixed vector in a module of
sequences over a dihedral group algebra with matrix coefficients.

## Background and reuse

The implementation uses Mathlib's individual torsion ideals, scalar module and
submodule annihilators, and its commutative set-torsion membership interface.
It reuses the ordered-product and augmentation nilpotence results in this
library rather than proving another finite-group bound. For classical modular
group-ring background see D. S. Passman, *The Algebraic Structure of Group
Rings*, Wiley, 1977. The common-vector argument above is stated at the more
general level of uniformly nilpotent actions of left ideals on semimodules.
