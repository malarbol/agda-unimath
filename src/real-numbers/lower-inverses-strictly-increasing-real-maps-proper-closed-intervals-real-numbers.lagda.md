# Lower inverses of strictly increasing real functions on proper closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.lower-inverses-strictly-increasing-real-maps-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.disjoint-subtypes
open import foundation.double-negation
open import foundation.embeddings
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.order-preserving-maps-preorders
open import order-theory.strict-order-preserving-maps
open import order-theory.strict-subpreorders
open import order-theory.subpreorders

open import real-numbers.binary-maximum-real-numbers
open import real-numbers.binary-minimum-real-numbers
open import real-numbers.clamp-function-closed-interval-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.maps-between-proper-closed-intervals-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-maps-proper-closed-intervals-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strictly-increasing-real-maps-proper-closed-intervals-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

Lower inverses

## Definitions

### The lower inverse of a strictly increasing map on a proper closed interval

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( I : proper-closed-interval-ℝ l3 l4)
  ( f : real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  ( H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  ( y@(v , lo-bound , hi-bound) :
    type-proper-closed-interval-ℝ
      ( l2)
      ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)))
  where

  lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    subtype (l2 ⊔ l4) ℚ
  lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    r =
    ∃ ℚ
      ( λ q →
        ( le-ℚ-Prop r q) ∧
        ( lower-cut-ℝ
          ( upper-bound-proper-closed-interval-ℝ I)
          ( q)) ∧
        ( leq-prop-ℝ
          ( clamp-real-map-proper-closed-interval-ℝ I f
            ( raise-real-ℚ l1 q))
          ( v)))

  is-in-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    ℚ → UU (l2 ⊔ l4)
  is-in-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    =
    type-Prop ∘
    lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ

  abstract opaque
    unfolding le-ℝ

    is-in-lower-cut-map-inv-le-lower-bound-is-strictly-increasing-real-map-properd-closed-interval-ℝ :
      (r : ℚ) →
      le-ℝ (real-ℚ r) (lower-bound-proper-closed-interval-ℝ I) →
      is-in-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( r)
    is-in-lower-cut-map-inv-le-lower-bound-is-strictly-increasing-real-map-properd-closed-interval-ℝ
      r r<a =
      let
        open
          do-syntax-trunc-Prop
            ( lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( r))
      in do
        ( q , r<q , q<a) ← r<a
        let
          lemma-r<q : le-ℚ r q
          lemma-r<q =
            reflects-le-real-ℚ
                ( le-real-is-in-upper-cut-ℝ (real-ℚ r) r<q)

          lemma-q≤a :
            leq-ℝ
              ( raise-real-ℚ l1 q)
              ( lower-bound-proper-closed-interval-ℝ I)
          lemma-q≤a =
            leq-le-ℝ
              ( le-raise-real-is-in-lower-cut-ℝ
                ( l1)
                ( lower-bound-proper-closed-interval-ℝ I)
                ( q<a))

          lemma-leq-clamp-fq :
            leq-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I f
                ( raise-real-ℚ l1 q))
              ( lower-bound-proper-closed-interval-ℝ
                ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                  ( I)
                  ( f)
                  ( H)))
          lemma-leq-clamp-fq =
            is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( I)
              ( f)
              ( H)
              ( _)
              ( _)
              ( preserves-leq-right-sim-ℝ
                ( sim-raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
                  ( I)
                  ( l1))
                ( leq-sim-ℝ
                  (clamp-leq-lower-bound-closed-interval-ℝ
                    ( closed-interval-proper-closed-interval-ℝ I)
                    ( raise-real-ℚ l1 q)
                    ( lemma-q≤a))))

          lemma-leq :
            leq-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I f
                ( raise-real-ℚ l1 q))
              ( v)
          lemma-leq =
            transitive-leq-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I f
                ( raise-real-ℚ l1 q))
              ( lower-bound-proper-closed-interval-ℝ
                ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                  ( I)
                  ( f)
                  ( H)))
              ( v)
              ( lo-bound)
              ( lemma-leq-clamp-fq)

          lemma-le :
            is-in-lower-cut-ℝ
              ( upper-bound-proper-closed-interval-ℝ I)
              ( q)
          lemma-le =
            is-in-lower-cut-le-real-ℚ
              ( upper-bound-proper-closed-interval-ℝ I)
              ( transitive-le-ℝ
                ( real-ℚ q)
                ( lower-bound-proper-closed-interval-ℝ I)
                ( upper-bound-proper-closed-interval-ℝ I)
                ( le-bounds-proper-closed-interval-ℝ I)
                ( le-real-is-in-lower-cut-ℝ
                  ( lower-bound-proper-closed-interval-ℝ I)
                  ( q<a)))

        intro-exists q (lemma-r<q , lemma-le , lemma-leq)

  abstract
    is-inhabited-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      is-inhabited-subtype
        lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    is-inhabited-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      =
      let
        open
          do-syntax-trunc-Prop
            ( is-inhabited-subtype-Prop
              ( lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ))
      in do
        ( r , r<a) ←
          exists-lesser-rational-ℝ (lower-bound-proper-closed-interval-ℝ I)

        intro-exists r
          ( is-in-lower-cut-map-inv-le-lower-bound-is-strictly-increasing-real-map-properd-closed-interval-ℝ
            ( r)
            ( r<a))

    is-lower-set-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      (q r : ℚ) →
      le-ℚ q r →
      is-in-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( r) →
      is-in-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( q)
    is-lower-set-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      q r q<r low =
      let
        open
          do-syntax-trunc-Prop
            ( lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( q))
      in do
        ( s , r<s , K) ← low

        intro-exists s (transitive-le-ℚ q r s r<s q<r , K)

    is-upper-rounded-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      (q : ℚ) →
      is-in-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( q) →
      exists
        ( ℚ)
        ( λ r →
          product-Prop
            ( le-ℚ-Prop q r)
            ( lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( r)))
    is-upper-rounded-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      q low =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ
                ( λ r →
                  product-Prop
                    ( le-ℚ-Prop q r)
                    ( lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                      ( r))))
      in do
        ( r , q<r , K) ← low
        ( s , q<s , s<r) ← dense-le-ℚ q<r

        intro-exists s (q<s , intro-exists r (s<r , K))

    is-rounded-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      (q : ℚ) →
      is-in-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( q) ↔
      exists
        ( ℚ)
        ( λ r →
          product-Prop
            ( le-ℚ-Prop q r)
            ( lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( r)))
    is-rounded-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      q =
      ( is-upper-rounded-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( q) ,
        elim-exists
          ( lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( q))
          ( λ r K →
            is-lower-set-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( q)
              ( r)
              ( pr1 K)
              ( pr2 K)))

    is-lower-dedekind-cut-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      is-lower-dedekind-cut
        lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    is-lower-dedekind-cut-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      =
      ( is-inhabited-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ ,
        is-rounded-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ)

  lower-real-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    lower-ℝ (l2 ⊔ l4)
  lower-real-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ =
    ( lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ ,
      is-lower-dedekind-cut-lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ)
```

## Properties

### The image of a rational in the lower cut of the lower inverse at a point is lesser than or equal to it

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( I : proper-closed-interval-ℝ l3 l4)
  ( f : real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  ( H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  ( y@(v , lo-bound , hi-bound) :
    type-proper-closed-interval-ℝ
      ( l2)
      ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)))
  where abstract

  leq-map-is-in-lower-cut-map-inv-le-lower-bound-is-strictly-increasing-real-map-properd-closed-interval-ℝ :
    (r : ℚ) →
    is-in-cut-lower-ℝ
      ( lower-real-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( y))
      ( r) →
    leq-ℝ
      ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l1 r))
      ( v)
  leq-map-is-in-lower-cut-map-inv-le-lower-bound-is-strictly-increasing-real-map-properd-closed-interval-ℝ
    r lo =
    let
      open
        do-syntax-trunc-Prop
          ( leq-prop-ℝ
            ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l1 r))
            ( v))
    in do
      (q , r<q , q<b , Hq) ← lo

      transitive-leq-ℝ
        ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l1 r))
        ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l1 q))
        ( v)
        ( Hq)
        ( is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( _)
          ( _)
          ( is-increasing-map-clamp-closed-interval-ℝ
            ( closed-interval-proper-closed-interval-ℝ I)
            ( _)
            ( _)
            ( leq-raise-leq-ℝ l1 (leq-le-ℝ (preserves-le-real-ℚ r<q)))))
```
