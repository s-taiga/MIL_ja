-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

/- TEXT:

Vector spaces and linear maps
-----------------------------

Vector spaces
^^^^^^^^^^^^^

.. index:: vector space

We will start directly abstract linear algebra, taking place in a vector space over any field.
However you can find information about matrices in :numref:`Section %s
<matrices>` which does not logically depend on this abstract theory.
Mathlib actually deals with a more general version of linear algebra involving the word module,
but for now we will pretend this is only an excentric spelling habit.

The way to say “let :math:`K` be a field and let $`V`$ be a vector space over $`K`$” is:

EXAMPLES: -/

-- QUOTE:

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
-- QUOTE.

/- TEXT:
We explained in :numref:`Chapter %s <hierarchies>` why we need two separate
typeclasses ``[AddCommGroup V] [Module K V]``.
The short version is the following.
Mathematically we want to say that having a :math:`K`-vector space structure
implies having an additive commutative group structure.
We could tell this to Lean. But then whenever Lean would need to find such a
group structure on a type :math:`V`, it would go hunting for vector space
structures using a *completely unspecified* field :math:`K` that cannot be infered
from :math:`V`.
This would be very bad for the type class synthesis system.

The multiplication of a vector `v` by a scalar `a` is denoted by
`a • v`. We a couple of algebraic rules about the interaction of this operation with addition in the
following examples. Of course `simp` of `apply?` would find those proofs, but it is still useful to
remember than scalar multiplication is abbreviated `smul` in lemma names.
Unfortunately there is not yet an analogue of the `ring` or `group` tactic that would prove
all equalities following from the vector space axioms (there is no deep obstruction here, we
simply need to find a skilled tactic writer having time for this).

EXAMPLES: -/

-- QUOTE:
example (a : K) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_add a u v

example (a b : K) (u : V) : (a + b) • u = a • u + b • u :=
  add_smul a b u

example (a b : K) (u : V) : a • b • u = b • a • u :=
  smul_comm a b u

-- QUOTE.

/- TEXT:
Linear maps
^^^^^^^^^^^

.. index:: linear map

Next we need linear maps. Like group morphisms, linear maps in Mathlib are bundled maps, ie packages
made of a map and proofs of its linearity properties.
Those bundled maps are converted to ordinary functions when applied.
See :numref:`Chapter %s <hierarchies>` for more information about this design.

The type of linear maps between two ``K``-vector spaces
``V`` and ``W`` is denoted by ``V →ₗ[K] W``. The subscript `l` stands for linear.
At first it may feel odd to specify ``K`` in this notation.
But this is crucial when several fields come into play.
For instance real-linear maps from :math:`ℂ` to $`ℂ`$ are every map $`z ↦ az + b\bar{z}`$
while only the maps :math:`z ↦ az` are complex linear, and this difference is crucial in
complex analysis.

EXAMPLES: -/
-- QUOTE:

variable {W : Type*} [AddCommGroup W] [Module K W]

variable (φ : V →ₗ[K] W)

example (a : K) (v : V) : φ (a • v) = a • φ v :=
  map_smul φ a v

example (v w : V) : φ (v + w) = φ v + φ w :=
  map_add φ v w

-- QUOTE.

/- TEXT:
Note that ``V →ₗ[K] W`` itself carries interesting algebraic structures (this
is part of the motivation for bundling those maps).

EXAMPLES: -/
-- QUOTE:
variable (ψ : V →ₗ[K] W)

#check (2 • φ + ψ : V →ₗ[K] W)

-- QUOTE.

/- TEXT:
One down-side of using bundled maps is that we cannot use ordinary function composition.
We need to use ``LinearMap.comp`` or the notation ``∘ₗ``.

EXAMPLES: -/
-- QUOTE:
variable (θ : W →ₗ[K] V)

#check (φ.comp θ : W →ₗ[K] W)
#check (φ ∘ₗ θ : W →ₗ[K] W)
-- QUOTE.

/- TEXT:
There are two main ways to construct linear maps.
First you can build the structure by providing the function and the linearity proof.
As usual, this is facilitated by the structure code action: you can type
``example : V →ₗ[K] V := _`` and use the code action “Generate a skeleton” attached to the
underscore.
EXAMPLES: -/
-- QUOTE:

example : V →ₗ[K] V where
  toFun v := 3 • v
  map_add' _ _ := smul_add ..
  map_smul' _ _ := smul_comm ..

-- QUOTE.

/- TEXT:
You may wonder why the proof fields of ``LinearMap`` have names ending with a prime.
This is because they are defined before the coercion to functions is defined, hence they are
phrased in terms of ``LinearMap.toFun``. Then they are restated as ``LinearMap.map_add``
and ``LinearMap.smul`` in terms of the coercion to function.
This is not yet the end of the story. One also want a version of ``map_add`` that applies to
any (bundled) map preserving addition, such as additive group morphisms, linear maps, continuous
linear maps, ``K``-algebra maps etc… This one is ``map_add`` (in the root namespace).
The intermediate version, ``LinearMap.map_add`` is a bit redudant but allows to use dot notation, which
can be nice sometimes. A similar story exists for ``map_smul``, and the general framework
is explained in :numref:`Chapter %s <hierarchies>`.
EXAMPLES: -/
-- QUOTE:

#check φ.map_add'
#check φ.map_add
#check map_add φ

-- QUOTE.

/- TEXT:
One can also build linear maps from the ones that are already defined in Mathlib
using various combinators.
For instance the above example is already known as ``LinearMap.lsmul K V 3``.
There are several reason why ``K`` and ``V`` are explicit arguments here.
The most pressing one is that from a bare ``LinearMap.lsmul 3`` there would be no way
for Lean to infer ``V`` or even ``K``.
But also ``LinearMap.lsmul K V`` is an interesting object by itself: it has type
``K →ₗ[K] V →ₗ[K] V``, meaning it is a ``K``-linear map from ``K``
—seen as a vector space over itself— to the space of ``K``-linear maps from ``V`` to ``V``.
EXAMPLES: -/
-- QUOTE:

#check LinearMap.lsmul K V 3
#check LinearMap.lsmul K V

-- QUOTE.

/- TEXT:
There is also a type ``LinearEquiv`` of linear isomorphisms denoted by ``V ≃ₗ[K] W``.
The inverse of ``f : V ≃ₗ[K] W`` is ``f.symm : W ≃ₗ[K] V``,
composition of ``f`` and ``g`` is ``f.trans g`` also denoted by ``f ≪≫ₗ g``, and
the identity isomorphism of ``V`` is ``LinearEquiv.refl K V``.
Elements of this type are automatically coerced to morphisms and functions when necessary.
EXAMPLES: -/
-- QUOTE:
example (f : V ≃ₗ[K] W) :
    f ≪≫ₗ f.symm = LinearEquiv.refl K V :=
  f.self_trans_symm
-- QUOTE.

/- TEXT:
One can use ``LinearEquiv.ofBijective`` to build an isomorphism from a bijective morphism.
Doing so makes the inverse function noncomputable.
EXAMPLES: -/
-- QUOTE:
noncomputable example (f : V →ₗ[K] W) (h : Function.Bijective f) : V ≃ₗ[K] W :=
  .ofBijective f h
-- QUOTE.

/- TEXT:
Sums and products of vector spaces
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We can also build new vector spaces out of old ones using direct sums and direct
products (we will discuss tensor products below after discussing multi-linear maps).
Let us start with two vectors spaces. In this case there is no difference between sum and product,
and we can simply use the product type.
In the following snippet of code we simply show how to get all the structure maps (inclusions
and projections) as linear maps, as well as the universal properties constructing linear maps
into products and out of sums (if you are not familiar with the category-theoretic distinction
between sums and products, you can simply ignore the universal property vocabulary and focus
on the types of the following examples).
EXAMPLES: -/
-- QUOTE:

section binary_product

variable {W : Type*} [AddCommGroup W] [Module K W]
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {T : Type*} [AddCommGroup T] [Module K T]

-- First projection map
example : V × W →ₗ[K] V := LinearMap.fst K V W

-- Second projection map
example : V × W →ₗ[K] W := LinearMap.snd K V W

-- Universal property of the product
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : U →ₗ[K]  V × W := LinearMap.prod φ ψ

-- The product map does the expected thing, first component
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.fst K V W ∘ₗ LinearMap.prod φ ψ = φ := rfl

-- The product map does the expected thing, second component
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.snd K V W ∘ₗ LinearMap.prod φ ψ = ψ := rfl

-- We can also combine maps in parallel
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) : (V × W) →ₗ[K] (U × T) := φ.prodMap ψ

-- This is simply done by combining the projections with the universal property
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) :
  φ.prodMap ψ = (φ ∘ₗ .fst K V W).prod (ψ ∘ₗ.snd K V W) := rfl

-- First inclusion map
example : V →ₗ[K] V × W := LinearMap.inl K V W

-- Second inclusion map
example : W →ₗ[K] V × W := LinearMap.inr K V W

-- Universal property of the sum (aka coproduct)
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : V × W →ₗ[K] U := φ.coprod ψ

-- The coproduct map does the expected thing, first component
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inl K V W = φ :=
  LinearMap.coprod_inl φ ψ

-- The coproduct map does the expected thing, second component
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inr K V W = ψ :=
  LinearMap.coprod_inr φ ψ



end binary_product

-- QUOTE.
/- TEXT:
Let us now turn to sums and products of arbitrary families of vector spaces.
Here we will simply see how to define a family of vector spaces and access the universal
properties of sums and products.
Note that the direct sum notation is scoped to the ``DirectSum`` namespace, and
that the universal property of direct sums requires decidable equality on the
indexing type (this is somehow an implementation accident).
EXAMPLES: -/

-- QUOTE:
section families
open DirectSum

variable {ι : Type*} [DecidableEq ι] (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

example (φ : Π i, V i →ₗ[K] W) : (⨁ i, V i) →ₗ[K] W :=
  DirectSum.toModule K ι W φ


example (φ : Π i, W →ₗ[K] V i) : W →ₗ[K] (Π i, V i) :=
  LinearMap.pi φ

example (i : ι) : (Π j, V j) →ₗ[K] V i := LinearMap.proj i

example : Π i, V i →+ (⨁ i, V i) := DirectSum.of V

example : Π i, V i →ₗ[K] (⨁ i, V i) := DirectSum.lof K ι V

variable (i : ι) in
#check LinearMap.single (R := K) (φ := V) i  -- The linear inclusion of V i into the product

variable (i : ι) in
#check DirectSum.lof K ι V i -- The linear inclusion of V i into the sum

example [Fintype ι] : (⨁ i, V i) ≃ₗ[K] (Π i, V i) :=
  linearEquivFunOnFintype K ι V

end families
-- QUOTE.
