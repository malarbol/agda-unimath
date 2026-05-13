# Inverses of strictly increasing real functions on proper closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.inverses-strictly-increasing-real-maps-proper-closed-intervals-real-numbers where
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
open import foundation.disjunction
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
open import real-numbers.lower-inverses-strictly-increasing-real-maps-proper-closed-intervals-real-numbers
open import real-numbers.maps-between-proper-closed-intervals-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-maps-proper-closed-intervals-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strictly-increasing-real-maps-proper-closed-intervals-real-numbers
open import real-numbers.upper-dedekind-real-numbers
open import real-numbers.upper-inverses-strictly-increasing-real-maps-proper-closed-intervals-real-numbers
```

</details>

## Idea

For any
[strictly increasing map](real-numbers.strictly-increasing-real-maps-proper-closed-intervals-real-numbers.md)
`f : [a, b] → ℝ` on a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
and any `y : [f(a) , f(b)]`, the
[lower](real-numbers.lower-inverses-strictly-increasing-real-maps-proper-closed-intervals-real-numbers.md)
and
[upper](real-numbers.upper-inverses-strictly-increasing-real-maps-proper-closed-intervals-real-numbers.md)
inverses of `f` at `y` are [disjoint](foundation.disjoint-subtypes.md) and
located [Dedekind cuts](real-numbers.dedekind-real-numbers.md) so they define a
real map:

```text
   f⁻¹ : [f(a), f(b)] → ℝ
```

TODO:

- prove that `f⁻¹` **is** an inverse of `f`.

## Propositions

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
          ( ( leq-le-ℝ
              ( le-real-is-in-upper-cut-ℝ
                ( lower-bound-proper-closed-interval-ℝ I)
                ( a<s))) ,
            ( leq-le-ℝ
              ( transitive-le-ℝ
                ( real-ℚ s)
                ( real-ℚ q)
                ( upper-bound-proper-closed-interval-ℝ I)
                ( le-real-is-in-lower-cut-ℝ
                  ( upper-bound-proper-closed-interval-ℝ I)
                  ( q<b))
                ( preserves-le-real-ℚ lemma-s<q))))

        is-in-interval-q :
          is-in-proper-closed-interval-ℝ I (real-ℚ q)
        is-in-interval-q =
          ( ( leq-le-ℝ
              ( transitive-le-ℝ
                ( lower-bound-proper-closed-interval-ℝ I)
                ( real-ℚ s)
                ( real-ℚ q)
                ( preserves-le-real-ℚ lemma-s<q)
                  ( le-real-is-in-upper-cut-ℝ
                  ( lower-bound-proper-closed-interval-ℝ I)
                  ( a<s)))) ,
            ( leq-le-ℝ
              ( le-real-is-in-lower-cut-ℝ
                ( upper-bound-proper-closed-interval-ℝ I)
                ( q<b))))

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

### The lower and upper inverses of a strictly increasing map is a located pair of cuts

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

  is-located-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-located-lower-upper-ℝ
      ( lower-real-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( y))
      ( upper-real-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( y))
  is-located-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    q r q<r =
    elim-disjunction
      ( ( lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( y)
          ( q)) ∨
        ( upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( y)
          ( r)))
      ( λ q<a →
        inl-disjunction
          ( is-in-lower-cut-map-inv-le-lower-bound-is-strictly-increasing-real-map-properd-closed-interval-ℝ
            ( I)
            ( f)
            ( H)
            ( y)
            ( q)
            ( le-real-is-in-lower-cut-ℝ
              ( lower-bound-proper-closed-interval-ℝ I)
              ( q<a))))
      ( elim-disjunction _
        ( λ b<r →
          inr-disjunction
            ( is-in-upper-cut-map-inv-le-upper-bound-is-strictly-increasing-real-map-properd-closed-interval-ℝ
              ( I)
              ( f)
              ( H)
              ( y)
              ( r)
              ( le-real-is-in-upper-cut-ℝ
                ( upper-bound-proper-closed-interval-ℝ I)
                ( b<r))))
        ( elim-exists _
          ( λ p →
            elim-exists _
              ( λ s (a<p , s<b , p<s , q<p , s<r) →
                elim-disjunction
                  ( ( lower-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                            ( I)
                            ( f)
                            ( H)
                            ( y)
                            ( q)) ∨
                    ( upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                      ( I)
                      ( f)
                      ( H)
                      ( y)
                      ( r)))
                  ( λ lo →
                    inl-disjunction
                      ( intro-exists p
                        ( q<p ,
                          is-in-lower-cut-le-real-ℚ
                            ( upper-bound-proper-closed-interval-ℝ I)
                            ( transitive-le-ℝ
                              ( real-ℚ p)
                              ( real-ℚ s)
                              ( upper-bound-proper-closed-interval-ℝ I)
                              ( le-real-is-in-lower-cut-ℝ
                                ( upper-bound-proper-closed-interval-ℝ I)
                                ( s<b))
                              ( preserves-le-real-ℚ p<s)) ,
                          leq-le-ℝ lo)))
                  ( λ hi →
                    inr-disjunction
                      ( intro-exists s
                        ( s<r ,
                          is-in-upper-cut-le-real-ℚ
                            ( lower-bound-proper-closed-interval-ℝ I)
                            ( transitive-le-ℝ
                              ( lower-bound-proper-closed-interval-ℝ I)
                              ( real-ℚ p)
                              ( real-ℚ s)
                              ( preserves-le-real-ℚ p<s)
                              ( le-real-is-in-upper-cut-ℝ
                                ( lower-bound-proper-closed-interval-ℝ I)
                                ( a<p))) ,
                          leq-le-ℝ hi)))
                  ( cotransitive-le-ℝ
                    ( clamp-real-map-proper-closed-interval-ℝ I f
                      ( raise-real-ℚ l1 p))
                    ( v)
                    ( clamp-real-map-proper-closed-interval-ℝ I f
                      ( raise-real-ℚ l1 s))
                    ( lemma-located-cut-map-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                      ( I)
                      ( f)
                      ( H)
                      ( raise-real-ℚ l1 p)
                      ( raise-real-ℚ l1 s)
                      ( is-in-proper-closed-interval-sim-ℝ I
                        ( sim-raise-ℝ l1 (real-ℚ p))
                        ( ( leq-le-ℝ
                            ( le-real-is-in-upper-cut-ℝ
                              ( lower-bound-proper-closed-interval-ℝ I)
                              ( a<p))) ,
                          ( leq-le-ℝ
                            ( transitive-le-ℝ
                              ( real-ℚ p)
                              ( real-ℚ s)
                              ( upper-bound-proper-closed-interval-ℝ I)
                              ( le-real-is-in-lower-cut-ℝ
                                ( upper-bound-proper-closed-interval-ℝ I)
                                ( s<b))
                              ( preserves-le-real-ℚ p<s)))))
                      ( is-in-proper-closed-interval-sim-ℝ I
                        ( sim-raise-ℝ l1 (real-ℚ s))
                        ( ( leq-le-ℝ
                            ( transitive-le-ℝ
                              ( lower-bound-proper-closed-interval-ℝ I)
                              ( real-ℚ p)
                              ( real-ℚ s)
                              ( preserves-le-real-ℚ p<s)
                              ( le-real-is-in-upper-cut-ℝ
                                ( lower-bound-proper-closed-interval-ℝ I)
                                ( a<p)))) ,
                          ( leq-le-ℝ
                            ( le-real-is-in-lower-cut-ℝ
                              ( upper-bound-proper-closed-interval-ℝ I)
                              ( s<b)))))
                      ( le-raise-le-ℝ l1 (preserves-le-real-ℚ p<s))))))))
      ( lemma-trichotomy-le-rational-proper-closed-interval-ℝ I q r q<r)
```

## Definition

### The inverse of a strictly increasing map on a proper closed interval

```agda
module _
  { l l1 l2 : Level}
  ( I : proper-closed-interval-ℝ l1 l2)
  ( f : real-map-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) (l ⊔ l1 ⊔ l2) I)
  ( H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  ( y@(v , lo-bound , hi-bound) :
    type-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)))
  where

  map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    ℝ (l ⊔ l1 ⊔ l2)
  pr1 map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ =
    lower-real-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( I)
      ( f)
      ( H)
      ( y)
  pr1 (pr2 map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ) =
    upper-real-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( I)
      ( f)
      ( H)
      ( y)
  pr2 (pr2 map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ) =
    ( ( is-disjoint-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( y)) ,
      ( is-located-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( y)))
```

## Properties

### The inverse function takes value in the original interval

```agda
module _
  { l l1 l2 : Level}
  ( I : proper-closed-interval-ℝ l1 l2)
  ( f : real-map-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) (l ⊔ l1 ⊔ l2) I)
  ( H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  ( y@(v , lo-bound , hi-bound) :
    type-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)))
  where

  abstract opaque
    unfolding leq-ℝ

    leq-lower-bound-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      leq-ℝ
        ( lower-bound-proper-closed-interval-ℝ I)
        ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( y))
    leq-lower-bound-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      q q<a =
      is-in-lower-cut-map-inv-le-lower-bound-is-strictly-increasing-real-map-properd-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( y)
        ( q)
        ( le-real-is-in-lower-cut-ℝ
          ( lower-bound-proper-closed-interval-ℝ I)
          ( q<a))

  abstract opaque
    unfolding leq-ℝ'

    leq-upper-bound-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      leq-ℝ
        ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( y))
        ( upper-bound-proper-closed-interval-ℝ I)
    leq-upper-bound-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      =
      leq-leq'-ℝ
        ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( y))
        ( upper-bound-proper-closed-interval-ℝ I)
        ( λ r b<r →
          is-in-upper-cut-map-inv-le-upper-bound-is-strictly-increasing-real-map-properd-closed-interval-ℝ
            ( I)
            ( f)
            ( H)
            ( y)
            ( r)
            ( le-real-is-in-upper-cut-ℝ
              ( upper-bound-proper-closed-interval-ℝ I)
              ( b<r)))

  abstract
    is-in-interval-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      is-in-proper-closed-interval-ℝ I
        ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( y))
    is-in-interval-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      =
      ( leq-lower-bound-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ ,
        leq-upper-bound-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ)

  in-interval-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I
  pr1
    in-interval-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    =
    map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ I f H y
  pr2
    in-interval-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    =
    is-in-interval-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
```
