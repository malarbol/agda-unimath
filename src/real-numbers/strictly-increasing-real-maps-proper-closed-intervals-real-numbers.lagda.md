# Strictly increasing real functions on proper closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.strictly-increasing-real-maps-proper-closed-intervals-real-numbers where
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
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

A [real map](real-numbers.real-maps-proper-closed-intervals-real-numbers.md) `f`
on a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
of [real numbers](real-numbers.dedekind-real-numbers.md) `[a, b]` is
{{#concept "strictly increasing" Disambiguation="real map on proper closerd interval of real numbers" Agda=is-strictly-increasing-real-map-proper-closed-interval-ℝ}}
if, for any `x , y ∈ [a, b]`, if `x < y`, then `f x < f y`.

## Definitions

### The property of being a strictly increasing real map on a proper closed interval

```agda
module _
  {l1 l2 l3 l4 : Level}
  (I : proper-closed-interval-ℝ l3 l4)
  where

  is-strictly-increasing-prop-real-map-proper-closed-interval-ℝ :
    real-map-proper-closed-interval-ℝ l1 l2 I →
    Prop (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-strictly-increasing-prop-real-map-proper-closed-interval-ℝ =
    preserves-strict-order-prop-map-Strict-Preorder
      ( strict-preorder-Strict-Subpreorder
        ( strict-preorder-ℝ l1)
        ( subtype-proper-closed-interval-ℝ l1 I))
      ( strict-preorder-ℝ l2)

  is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    real-map-proper-closed-interval-ℝ l1 l2 I →
    UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-strictly-increasing-real-map-proper-closed-interval-ℝ =
    type-Prop ∘ is-strictly-increasing-prop-real-map-proper-closed-interval-ℝ

  is-prop-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    (f : real-map-proper-closed-interval-ℝ l1 l2 I) →
    is-prop (is-strictly-increasing-real-map-proper-closed-interval-ℝ f)
  is-prop-is-strictly-increasing-real-map-proper-closed-interval-ℝ =
    is-prop-type-Prop ∘
    is-strictly-increasing-prop-real-map-proper-closed-interval-ℝ
```

## Properties

### A strictly increasing map on a proper closed interval is increasing

```agda
module _
  {l1 l2 l3 l4 : Level}
  (I : proper-closed-interval-ℝ l3 l4)
  (f : real-map-proper-closed-interval-ℝ l1 l2 I)
  where abstract

  is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-strictly-increasing-real-map-proper-closed-interval-ℝ I f →
    preserves-order-Preorder
      ( preorder-Subpreorder
        ( ℝ-Preorder l1)
        ( subtype-proper-closed-interval-ℝ l1 I))
      ( ℝ-Preorder l2)
      ( f)
  is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    H x@(u , _) y@(v , _) u≤v =
    double-negation-elim-leq-ℝ
      ( f x)
      ( f y)
      ( map-double-negation
        ( rec-coproduct
          ( λ u~v →
            leq-eq-ℝ
              ( ap f
                ( eq-type-subtype
                  ( subtype-proper-closed-interval-ℝ l1 I)
                  ( eq-sim-ℝ u~v))))
          ( λ u<v → leq-le-ℝ (H x y u<v)))
        ( irrefutable-sim-or-le-leq-ℝ u v u≤v))
```

### Strictly increasing maps on proper closed intervals reflect inequality

```agda
module _
  {l1 l2 l3 l4 : Level}
  (I : proper-closed-interval-ℝ l3 l4)
  (f : real-map-proper-closed-interval-ℝ l1 l2 I)
  (H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where abstract

  reflects-leq-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    ( x@(u , _) y@(v , _) : type-proper-closed-interval-ℝ l1 I) →
    leq-ℝ (f x) (f y) →
    leq-ℝ u v
  reflects-leq-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    x@(u , _) y@(v , _) K =
    leq-not-le-ℝ v u (not-le-leq-ℝ (f x) (f y) K ∘ (H y x))
```

### Strictly increasing maps on proper closed intervals are embeddings

```agda
module _
  {l1 l2 l3 l4 : Level}
  (I : proper-closed-interval-ℝ l3 l4)
  (f : real-map-proper-closed-interval-ℝ l1 l2 I)
  (H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where abstract

  is-injective-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-injective f
  is-injective-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    {x@(u , _)} {y@(v , _)} fx=fy =
    eq-type-subtype
      ( subtype-proper-closed-interval-ℝ l1 I)
      ( antisymmetric-leq-ℝ u v
        ( reflects-leq-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( x)
          ( y)
          ( leq-eq-ℝ fx=fy))
        ( reflects-leq-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( y)
          ( x)
          ( leq-eq-ℝ (inv fx=fy))))

  is-emb-is-strictly-increasing-real-map-proper-closed-interval-ℝ : is-emb f
  is-emb-is-strictly-increasing-real-map-proper-closed-interval-ℝ =
    is-emb-is-injective
      ( is-set-ℝ l2)
      ( is-injective-is-strictly-increasing-real-map-proper-closed-interval-ℝ)
```

### The images of the bounds of a proper closed interval by a strictly increasing map are strictly ordered

```agda
module _
  {l1 l2 l3 l4 : Level}
  (I : proper-closed-interval-ℝ l3 l4)
  (f : real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  (H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where

  abstract
    le-im-bounds-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      le-ℝ
        ( f
          ( raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
            ( I)
            ( l1)))
        ( f
          ( raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
            ( I)
            ( l1)))
    le-im-bounds-is-strictly-increasing-real-map-proper-closed-interval-ℝ =
      H
        ( raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
          ( I)
          ( l1))
        ( raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
          ( I)
          ( l1))
        ( preserves-le-sim-ℝ
          ( sim-raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
            ( I)
            ( l1))
          ( sim-raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
            ( I)
            ( l1))
          ( le-bounds-proper-closed-interval-ℝ I))

  proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    proper-closed-interval-ℝ l2 l2
  proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    =
    ( ( f
        ( raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
          ( I)
          ( l1))) ,
      ( f
        ( raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
          ( I)
          ( l1))) ,
      ( le-im-bounds-is-strictly-increasing-real-map-proper-closed-interval-ℝ))
```

### The image of a strictly increasing map on a proper closed interval is contained in the interval image of its bounds

```agda
module _
  {l1 l2 l3 l4 : Level}
  (I : proper-closed-interval-ℝ l3 l4)
  (f : real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  (H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where abstract

  is-in-proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    (x : type-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) I) →
    is-in-proper-closed-interval-ℝ
      ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H))
      ( f x)
  is-in-proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    x@(u , lo-bound , hi-bound) =
    ( ( is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
          ( I)
          ( l1))
        ( x)
        ( preserves-leq-left-sim-ℝ
          ( sim-raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
            ( I)
            ( l1))
          ( lo-bound))) ,
      ( is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( x)
        ( raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
          ( I)
          ( l1))
        ( preserves-leq-right-sim-ℝ
          ( sim-raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
            ( I)
            ( l1))
          ( hi-bound))))
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  (I : proper-closed-interval-ℝ l3 l4)
  (f : real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  (H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where

  map-proper-closed-interval-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    map-proper-closed-interval-ℝ _ _
      ( I)
      ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H))
  map-proper-closed-interval-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    x =
    ( f x ,
      is-in-proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( x))
```

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
        ( le-prop-ℝ
          ( real-ℚ q)
          ( upper-bound-proper-closed-interval-ℝ I)) ∧
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
            le-ℝ
              ( real-ℚ q)
              ( upper-bound-proper-closed-interval-ℝ I)
          lemma-le =
            transitive-le-ℝ
              ( real-ℚ q)
              ( lower-bound-proper-closed-interval-ℝ I)
              ( upper-bound-proper-closed-interval-ℝ I)
              ( le-bounds-proper-closed-interval-ℝ I)
              ( le-real-is-in-lower-cut-ℝ
                ( lower-bound-proper-closed-interval-ℝ I)
                ( q<a))

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

### The upper inverse of a strictly increasing map on a proper closed interval

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

  upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    subtype (l2 ⊔ l3) ℚ
  upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    r =
    ∃ ℚ
      ( λ q →
        ( le-ℚ-Prop q r) ∧
        ( le-prop-ℝ
          ( lower-bound-proper-closed-interval-ℝ I)
          ( real-ℚ q)) ∧
        ( leq-prop-ℝ
          ( v)
          ( clamp-real-map-proper-closed-interval-ℝ I f
            ( raise-real-ℚ l1 q))))

  is-in-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    ℚ → UU (l2 ⊔ l3)
  is-in-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    =
    type-Prop ∘
    upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ

  abstract opaque
    unfolding le-ℝ

    is-in-upper-cut-map-inv-le-upper-bound-is-strictly-increasing-real-map-properd-closed-interval-ℝ :
      (r : ℚ) →
      le-ℝ (upper-bound-proper-closed-interval-ℝ I) (real-ℚ r) →
      is-in-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( r)
    is-in-upper-cut-map-inv-le-upper-bound-is-strictly-increasing-real-map-properd-closed-interval-ℝ
      r b<r =
      let
        open
          do-syntax-trunc-Prop
            ( upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( r))
      in do
        ( q , b<q , q<r) ← b<r

        let
          lemma-q<r : le-ℚ q r
          lemma-q<r =
            reflects-le-real-ℚ
                ( le-real-is-in-lower-cut-ℝ (real-ℚ r) q<r)

          lemma-b≤q :
            leq-ℝ
              ( upper-bound-proper-closed-interval-ℝ I)
              ( raise-real-ℚ l1 q)
          lemma-b≤q =
            leq-le-ℝ
              ( le-raise-real-is-in-upper-cut-ℝ
                ( l1)
                ( upper-bound-proper-closed-interval-ℝ I)
                ( b<q))

          lemma-leq-clamp-fq :
            leq-ℝ
              ( upper-bound-proper-closed-interval-ℝ
                ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                  ( I)
                  ( f)
                  ( H)))
              ( clamp-real-map-proper-closed-interval-ℝ I f
                ( raise-real-ℚ l1 q))
          lemma-leq-clamp-fq =
            is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( I)
              ( f)
              ( H)
              ( _)
              ( _)
              ( preserves-leq-left-sim-ℝ
                ( sim-raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
                  ( I)
                  ( l1))
                ( leq-sim-ℝ
                  ( symmetric-sim-ℝ
                    ( clamp-leq-upper-bound-closed-interval-ℝ
                      ( closed-interval-proper-closed-interval-ℝ I)
                      ( raise-real-ℚ l1 q)
                      ( lemma-b≤q)))))
          lemma-leq :
            leq-ℝ
              ( v)
              ( clamp-real-map-proper-closed-interval-ℝ I f
                ( raise-real-ℚ l1 q))
          lemma-leq =
            transitive-leq-ℝ
              ( v)
              ( upper-bound-proper-closed-interval-ℝ
                ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                  ( I)
                  ( f)
                  ( H)))
              ( clamp-real-map-proper-closed-interval-ℝ I f
                ( raise-real-ℚ l1 q))
              ( lemma-leq-clamp-fq)
              ( hi-bound)

          lemma-le :
            le-ℝ (lower-bound-proper-closed-interval-ℝ I) (real-ℚ q)
          lemma-le =
            transitive-le-ℝ
              ( lower-bound-proper-closed-interval-ℝ I)
              ( upper-bound-proper-closed-interval-ℝ I)
              ( real-ℚ q)
              ( le-real-is-in-upper-cut-ℝ
                ( upper-bound-proper-closed-interval-ℝ I)
                ( b<q))
              ( le-bounds-proper-closed-interval-ℝ I)

        intro-exists q (lemma-q<r , lemma-le , lemma-leq)

  abstract
    is-inhabited-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      is-inhabited-subtype
        upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    is-inhabited-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      =
      let
        open
          do-syntax-trunc-Prop
            ( is-inhabited-subtype-Prop
              ( upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ))
      in do
        ( r , b<r) ←
          exists-greater-rational-ℝ (upper-bound-proper-closed-interval-ℝ I)

        intro-exists r
          ( is-in-upper-cut-map-inv-le-upper-bound-is-strictly-increasing-real-map-properd-closed-interval-ℝ
            ( r)
            ( b<r))

    is-upper-set-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      (q r : ℚ) →
      le-ℚ q r →
      is-in-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( q) →
      is-in-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( r)
    is-upper-set-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      q r q<r up =
      let
        open
          do-syntax-trunc-Prop
            ( upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( r))
      in do
        ( s , s<q , K) ← up

        intro-exists s (transitive-le-ℚ s q r q<r s<q , K)

    is-lower-rounded-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      (q : ℚ) →
      is-in-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( q) →
      exists
        ( ℚ)
        ( λ r →
          product-Prop
            ( le-ℚ-Prop r q)
            ( upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( r)))
    is-lower-rounded-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      q hi =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ
                ( λ r →
                  product-Prop
                    ( le-ℚ-Prop r q)
                    ( upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                      ( r))))
      in do
        ( r , r<q , K) ← hi
        ( s , r<s , s<q) ← dense-le-ℚ r<q

        intro-exists s (s<q , intro-exists r (r<s , K))

    is-rounded-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      (q : ℚ) →
      is-in-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( q) ↔
      exists
        ( ℚ)
        ( λ r →
          product-Prop
            ( le-ℚ-Prop r q)
            ( upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( r)))
    is-rounded-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      q =
      ( is-lower-rounded-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( q) ,
        elim-exists
          ( upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( q))
          ( λ r K →
            is-upper-set-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( r)
              ( q)
              ( pr1 K)
              ( pr2 K)))

    is-upper-dedekind-cut-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      is-upper-dedekind-cut
        upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    is-upper-dedekind-cut-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      =
      ( is-inhabited-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ ,
        is-rounded-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ)

  upper-real-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    upper-ℝ (l2 ⊔ l3)
  upper-real-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ =
    ( upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ ,
      is-upper-dedekind-cut-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ)
```

### The image of a rational in the upper cut of the inverse at a point is greater than or equal to it

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

  leq-map-is-in-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    ( r : ℚ) →
    ( is-in-cut-upper-ℝ
      ( upper-real-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( y))
      ( r)) →
    leq-ℝ
      ( v)
      ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l1 r))
  leq-map-is-in-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    r hi =
    let
      open
        do-syntax-trunc-Prop
          ( leq-prop-ℝ
            ( v)
            ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l1 r)))
    in do
      ( q , q<r , a<q , Hq) ← hi

      transitive-leq-ℝ
        ( v)
        ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l1 q))
        ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l1 r))
        (( is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( _)
          ( _)
          ( is-increasing-map-clamp-closed-interval-ℝ
            ( closed-interval-proper-closed-interval-ℝ I)
            ( _)
            ( _)
            ( leq-raise-leq-ℝ l1 (leq-le-ℝ (preserves-le-real-ℚ q<r))))))
        ( Hq)
```

### The lower and upper inverses of a strictly increasing map are disjoint cuts

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

  is-disjoint-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    disjoint-subtype
      ( lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( y))
      ( upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( y))
  is-disjoint-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    r (lo , hi) =
    let open do-syntax-trunc-Prop empty-Prop
    in do
      (q , r<q , q<b , Hq) ← lo
      (s , s<r , a<s , Hs) ← hi

      let
        lemma-leq-clamp-f-qs :
          leq-ℝ
            ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l1 q))
            ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l1 s))
        lemma-leq-clamp-f-qs = transitive-leq-ℝ _ _ _ Hs Hq

        lemma-leq-clamp-qs :
          leq-ℝ
            ( map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l1 q))
            ( map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l1 s))
        lemma-leq-clamp-qs =
          reflects-leq-is-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( I)
            ( f)
            ( H)
            ( _)
            ( _)
            ( lemma-leq-clamp-f-qs)

        lemma-s<q : le-ℚ s q
        lemma-s<q = transitive-le-ℚ s r q r<q s<r

        is-in-interval-s :
          is-in-proper-closed-interval-ℝ I (real-ℚ s)
        is-in-interval-s =
          ( leq-le-ℝ a<s ,
            leq-le-ℝ
              ( transitive-le-ℝ
                ( real-ℚ s)
                ( real-ℚ q)
                ( upper-bound-proper-closed-interval-ℝ I)
                ( q<b)
                ( preserves-le-real-ℚ lemma-s<q)))

        is-in-interval-q :
          is-in-proper-closed-interval-ℝ I (real-ℚ q)
        is-in-interval-q =
          ( leq-le-ℝ
            ( transitive-le-ℝ
              ( lower-bound-proper-closed-interval-ℝ I)
              ( real-ℚ s)
              ( real-ℚ q)
              ( preserves-le-real-ℚ lemma-s<q)
              ( a<s)) ,
            leq-le-ℝ q<b)

        compute-map-clamp-s :
          sim-ℝ
            ( map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l1 s))
            ( raise-real-ℚ l1 s)
        compute-map-clamp-s =
          clamp-is-in-closed-interval-ℝ
            ( closed-interval-proper-closed-interval-ℝ I)
            ( raise-real-ℚ l1 s)
            ( is-in-proper-closed-interval-sim-ℝ
              ( I)
              ( sim-raise-ℝ l1 (real-ℚ s))
              ( is-in-interval-s))

        compute-map-clamp-q :
          sim-ℝ
            ( map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l1 q))
            ( raise-real-ℚ l1 q)
        compute-map-clamp-q =
          clamp-is-in-closed-interval-ℝ
            ( closed-interval-proper-closed-interval-ℝ I)
            ( raise-real-ℚ l1 q)
            ( is-in-proper-closed-interval-sim-ℝ
              ( I)
              ( sim-raise-ℝ l1 (real-ℚ q))
              ( is-in-interval-q))

        lemma-eq-clamp-qs :
          map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l1 q) ＝
          map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l1 s)
        lemma-eq-clamp-qs =
          antisymmetric-leq-ℝ _ _
            ( lemma-leq-clamp-qs)
            ( is-increasing-map-clamp-closed-interval-ℝ
              ( closed-interval-proper-closed-interval-ℝ I)
              ( _)
              ( _)
              ( preserves-leq-sim-ℝ
                ( sim-raise-ℝ l1 (real-ℚ s))
                ( sim-raise-ℝ l1 (real-ℚ q))
                ( preserves-leq-real-ℚ
                  ( leq-le-ℚ
                    ( transitive-le-ℚ _ _ _ r<q s<r)))))

        lemma-s~q : raise-real-ℚ l1 s ~ℝ raise-real-ℚ l1 q
        lemma-s~q =
          symmetric-sim-ℝ
            ( transitive-sim-ℝ _ _ _
              ( concat-eq-sim-ℝ
                ( lemma-eq-clamp-qs)
                ( compute-map-clamp-s))
              ( symmetric-sim-ℝ compute-map-clamp-q))

      not-sim-le-ℝ
        ( le-raise-le-ℝ l1 (preserves-le-real-ℚ lemma-s<q))
        ( lemma-s~q)
```

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( I : proper-closed-interval-ℝ l3 l4)
  ( f : real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  ( H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where abstract

  lemma-located-cut-map-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    (x y : ℝ l1) →
    (x∈I : is-in-proper-closed-interval-ℝ I x) →
    (y∈I : is-in-proper-closed-interval-ℝ I y) →
    le-ℝ x y →
    le-ℝ
      ( clamp-real-map-proper-closed-interval-ℝ I f x)
      ( clamp-real-map-proper-closed-interval-ℝ I f y)
  lemma-located-cut-map-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    x y x∈I y∈I =
    H
      ( clamp-proper-closed-interval-ℝ I x)
      ( clamp-proper-closed-interval-ℝ I y) ∘
    le-map-clamp-le-is-in-closed-interval-ℝ
      ( closed-interval-proper-closed-interval-ℝ I)
      ( x)
      ( x∈I)
      ( y)
      ( y∈I)
```
