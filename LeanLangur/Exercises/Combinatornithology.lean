
import Lean

/-- The `use` tactic is for supplying a candidate value
    for an existential goal. -/
macro "use" t:term : tactic =>
  `(tactic| apply Exists.intro $t)

/-
  These logic puzzles are mainly inspired by the ones in the book
  "To Mock a Mockingbird", written by Raymond Smullyan.
-/

namespace EnchantedForest

  namespace Introduction
    /-!
    A certain enchanted forest in a mystical land far away
    is inhabited by talking birds.
    -/

    -- all birds in the enchanted forest belong to the type `Bird`
    -- a `Type` can be thought of as being similar to a `Set`
    axiom Bird : Type

    /-!
    Given any birds `A` and `B`, if the name of bird `B` is called out to `A`,
    then `A` responds with the name of another bird.
    -/

    -- `response A B` is the response of Bird `A` on hearing Bird `B`'s name
    axiom response : Bird → Bird → Bird

    -- better notation for denoting response
    -- the operator is left-associative
    -- the ` ◁ ` symbol (typed as `\lhd`) resembles an ear/beak
    infix:100 " ◁ " => response

  end Introduction

  open Introduction


  namespace IdentityBird
    /-!
      If the name of a bird `x` is called out to the identity bird `I`,
      it responds with just `x`.

      This bird is sometimes called the "Ibis", or also (rather rudely) as the
      "idiot bird".

      https://en.wikipedia.org/wiki/Ibis
    -/

    -- the definition of the identity bird
    axiom I : Bird
    axiom I.call : ∀ x : Bird, (I ◁ x) = x

  end IdentityBird


  /-!
  A bird `A` is said to be *fond* of another bird `B` if
  the bird `A` responds to the name `B` with the same name `B`.
  -/

  -- the definition of fondness
  notation A " is " " fond " " of " B => A ◁ B = B

  /-!
  A bird `E` is called *egocentric* if it is fond of itself.
  -/

  -- the definition of egocentricity
  notation E " is " " egocentric " => E ◁ E = E

  section DefendingTheIdentityBird
    open IdentityBird

    /-!
      Students of Combinatornithology sometimes rudely referred to the
      identity bird as the "idiot bird", because of its apparent simplicity.

      The theorems in this section show why the identity bird is actually quite
      intelligent.
    -/

    -- The identity bird is fond of every bird.
    theorem identity_fond_of_all : ∀ x : Bird, I is fond of x := by
     sorry

    -- The identity bird is egocentric.
    theorem identity_egocentric : I is egocentric := by
      sorry

    /-!
      The identity bird has an unusually large heart! It is fond of every bird.

      It is also egocentric, but it is fond of itself no more than it is of any
      other bird.
    -/
  end DefendingTheIdentityBird

  /-!
  A bird `B` is called *hopelessly egocentric* if
  for every bird `x`, `B ◁ x = B`.
  -/

  set_option quotPrecheck false in
  -- the definition of hopeless egocentricity
  notation B " is " " hopelessly " " egocentric " => ∀ x, B ◁ x = B

  /-!
  More generally, a bird `A` is *fixated* on a bird `B` if
  for every bird `x`, the response of `A` on hearing `x` is `B`.

  Thus a hopelessly egocentric bird is one that is fixated on itself.
  -/

  set_option quotPrecheck false in
  -- the definition of fixatedness
  notation A " is " " fixated " " on " B => ∀ x, A ◁ x = B


  namespace Kestrel
    /-!
      A bird `K` is a *kestrel* if for any bird `x`,
      the bird `K ◁ x` is fixated on `x`.

      https://en.wikipedia.org/wiki/Kestrel
    -/

    -- the definition of a kestrel
    axiom K : Bird
    axiom K.call : ∀ (x y : Bird), (K ◁ x) ◁ y = x

  end Kestrel

  section KestrelTheorems
    open Kestrel

    -- For any bird `x`, the bird `K ◁ x` is fixated on `x`.
    theorem k_x_fixated_on_x : ∀ x, (K ◁ x) is fixated on x := by
      sorry

    -- An egocentric kestrel must be hopelessly egocentric.
    theorem kestrel_egocentrism
        (kestrel_egocentric : K is egocentric) :
        (K is hopelessly egocentric) := by
      sorry

    -- The left cancellation law for kestrels.
    theorem kestrel_left_cancellation
        (x y : Bird)
        (kestrel_application : K ◁ x = K ◁ y) :
        (x = y) := by
      sorry

    -- `*` For an arbitrary bird `x`, if `K` is fond of `K ◁ x`,
    -- then `K` is fond of `x`.
    theorem kestrel_fondness
        (x : Bird)
        (fond_Kx : K is fond of (K ◁ x)) :
        K is fond of x := by
      sorry

  end KestrelTheorems

  /-!
  Two birds `A` and `B` form an *agreeable pair* if there is another bird `x`
  that they agree on, i.e., if their responses on hearing the name `x` are the same.
  (or in symbols,  (A ◁ x) = (B ◁ x))

  A bird `A` is *agreeable* if it forms an agreeable pair with every other bird `B`.
  -/

  -- the definition of agreeable birds

  notation A " is " " agreeable " " with " B => ∃ x : Bird, A ◁ x = B ◁ x
  set_option quotPrecheck false in
  notation A " is " " agreeable " => ∀ β : Bird, A is agreeable with β

  section IdentityBirdTheorems
    open IdentityBird

    -- If the forest contains an identity bird `I` that is agreeable,
    -- then every bird is fond of at least one bird.
    -- This does not rely on the composition axiom.
    theorem agreeable_identity_induces_fondness
        (I_agreeable : I is agreeable) :
        ∀ B, ∃ x, B is fond of x := by
      sorry

    -- `*` If every bird is fond of at least one bird, then
    -- the identity bird must be agreeable.
    theorem fondness_induces_agreeable_identity
        (all_birds_fond : ∀ B, ∃ x, B is fond of x) :
        I is agreeable := by
      sorry

  end IdentityBirdTheorems


  namespace Mockingbird
    /-!
      A *mockingbird* is a kind of bird whose response to any bird `x`
      is exactly the response of `x` to itself.

      https://en.wikipedia.org/wiki/Mockingbird
    -/

    -- the definition of a mockingbird
    axiom M : Bird
    axiom M.call : ∀ x, M ◁ x = x ◁ x

  end Mockingbird

  namespace ForestCompositionLaw
    /-!
    Given any birds `A`, `B`, `C`, the bird `C` is said to *compose*
    `A` with `B` if for every bird `x`, the following condition holds
                      (C ◁ x) = (A ◁ (B ◁ x))

    This part of the forest has the property that for any two birds
    `A` and `B`, there is a third bird `C` that composes `A` with `B`.
    -/

    -- composition of birds, implemented as a function similar to `response`
    axiom compose : Bird → Bird → Bird
    -- notation for composition
    infixr:100 " ∘ " => compose
    -- the definition of composition
    axiom composition (A B : Bird) : ∀ {x : Bird}, (A ∘ B) ◁ x = A ◁ (B ◁ x)

  end ForestCompositionLaw

  section MockingbirdTheorems
    open Mockingbird

    -- The mockingbird is agreeable.
    theorem mockingbird_agreeable : M is agreeable := by
      sorry

    open ForestCompositionLaw

    -- If a mockingbird is in the forest and the composition law holds,
    -- then every bird is fond of at least one bird.
    theorem mockingbird_induces_fondness : ∀ A, ∃ B, A is fond of B := by
      intro A

      use (A ∘ M) ◁ (A ∘ M)

      conv =>
        rhs
        -- place cursor here

      sorry

    -- If the composition law holds and a mockingbird is in the forest,
    -- then there is a bird that is egocentric.
    theorem exists_egocentric : ∃ E, E is egocentric := by
      sorry

    -- `*` If `A` is an agreeable bird and the composition law holds,
    -- every bird is fond of at least one bird.
    theorem agreeability_induces_fondness
        (α : Bird)
        (α_agreeable : α is agreeable)
        : ∀ A, ∃ B, A is fond of B := by
      sorry

    -- A proof of the earlier theorem as a corollary of the previous one.
    theorem mockingbird_agreeable_fondness : ∀ A, ∃ B, A is fond of B :=
      agreeability_induces_fondness M mockingbird_agreeable

  end MockingbirdTheorems

  namespace Bluebird
    /-!
      The *bluebird* `B` is a bird that can perform composition.

      For birds `x`, `y`, `z`, the following property holds:
            `(((B ◁ x) ◁ y) ◁ z) = x ◁ (y ◁ z)`

      https://en.wikipedia.org/wiki/Bluebird
    -/

    -- the definition of a bluebird
    axiom B : Bird
    axiom B.call : ∀ (x y z : Bird), (((B ◁ x) ◁ y) ◁ z) = x ◁ (y ◁ z)

  end Bluebird

  section BluebirdTheorems
    open Bluebird
    open ForestCompositionLaw

    -- The bluebird is capable of composing one bird with another.
    theorem bluebird_composition (x y : Bird) :
        ∀ z : Bird, ((B ◁ x) ◁ y) ◁ z = (x ∘ y) ◁ z := by
      sorry

    open Mockingbird

    -- If a mockingbird and a bluebird are in the forest,
    -- for every bird `A` in the forest, one can contruct a
    -- bird `β` using bird calls such that `A` is fond of `β`.
    theorem all_birds_fond : ∀ A, ∃ β, A is fond of β := by
      sorry

  end BluebirdTheorems

  namespace Lark
    /-!
      The *lark* `L` is a bird which, on hearing the name of an
      arbitrary bird `x`, calls out the name of the bird that
      composes `x` with the mockingbird `M`.

      https://en.wikipedia.org/wiki/Lark
    -/

    -- the definition of a lark
    axiom L : Bird
    axiom L.call : ∀ (x y : Bird), (L ◁ x) ◁ y = x ◁ (y ◁ y)

  end Lark

  namespace LarkTheorems
    open Lark

    -- `*` Every bird is fond of a hopelessly egocentric lark.
    theorem egocentric_lark_popular
      (egocentric_lark : L is egocentric) :
      ∀ β, β is fond of L :=
      sorry

  end LarkTheorems

  namespace Starling
    /-!
      A *starling* is a bird `S` that satisfies the following condition
          `(((S ◁ x) ◁ y) ◁ z) = (x ◁ z) ◁ (y ◁ z)`

      https://en.wikipedia.org/wiki/Starling
    -/

    -- definition of the starling
    axiom S : Bird
    axiom S.call : ∀ (x y z : Bird), (((S ◁ x) ◁ y) ◁ z) = (x ◁ z) ◁ (y ◁ z)
  end Starling

  section StarlingTheorems
    open Starling
    open Kestrel

    /-!
      The existence of a Starling and a Kestrel in the forest is
      sufficient to imply the existence of several other birds.
    -/

    -- Derive the identity bird.


    -- Derive the mockingbird.


    -- `*` Derive the bluebird.


  end StarlingTheorems

  section SummoningASagebird
    /-!
      According to folklore, a *sagebird* or an *oracle bird* `Θ` is
      believed to have the property that if the name of any bird `x` is
      called out to `θ`, it responds with the name of a bird that `x` is fond of.

      Interestingly, the existence of a sagebird can be deduced from the birds
      encountered so far.
    -/

    -- adding all the known birds
    open IdentityBird
    open Kestrel
    open Mockingbird
    open Bluebird
    open Lark
    open Starling

    -- a sage bird exists in the forest
    theorem sagebird_existence :
        ∃ θ, ∀ x, x ◁ (θ ◁ x) = θ ◁ x := by
      sorry

  end SummoningASagebird

end EnchantedForest

  /-!
    A star~t~ling fact:

    All birds can be derived from just the
    kestrel (`K`) and the
    starling (`S`)!

    # The algorithm

    Define the `α-eliminate` of an expression `E` to be
    an expression `F` such that `F α = E`.
    1. The α-eliminate of `α` is `I`.
    2. If `α` does not occur in `E`, then `K E` is the
        α-eliminate.
    3. If `E` is of the form `F α`, then `F` is the
        α-eliminate of `E`.
    4. If `E = F G`, and `F'` and `G'` are the corresponding
      α-eliminates of the expressions, then
          `S (F') (G')` is the corresponding α-eliminate.

    Repeated α-elimination of all the variables involved gives the
    expression for the bird in terms of `S` and `K`.

    For a recursive bird `U` (i.e., a bird whose call depends on itself),
    replace every occurrence of the letter `U` in the call with an unused
    variable name and solve as above.

    Call this modified bird `V`. It satisfies the property `V ◁ U = U`.

    Since the existence of the mockingbird and the bluebird is sufficient to
    guarantee that every bird is fond of some bird, one can find a bird `F` such that
    `V` is fond of `F`, that is, `V ◁ F = F`. But this is the property that `U` is required
    to satisfy. Thus `F`, which can be derived from `S` and `K` using the sage bird,
    is the required bird.
  -/

-- TO-DO
namespace Ornithologic
end Ornithologic

namespace AvianArithmetic
end AvianArithmetic

/-!
  # References:

  1. "To Mock a Mockingbird", by Raymond Smullyan (https://en.wikipedia.org/wiki/To_Mock_a_Mockingbird)
  2. "To Dissect a Mockingbird", by David Keenan (https://dkeenan.com/Lambda/index.htm)
  3. SKI Combinator calculus (https://en.wikipedia.org/wiki/SKI_combinator_calculus)
  4. The Natural Number Game (https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/)
-/
