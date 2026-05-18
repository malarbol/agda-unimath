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
open import foundation.binary-transport
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.disjoint-subtypes
open import foundation.disjunction
open import foundation.double-negation
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.metric-spaces
open import metric-spaces.pointwise-epsilon-delta-continuous-maps-metric-spaces

open import order-theory.order-preserving-maps-preorders
open import order-theory.strict-order-preserving-maps
open import order-theory.strict-subpreorders
open import order-theory.subpreorders

open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.binary-maximum-real-numbers
open import real-numbers.binary-minimum-real-numbers
open import real-numbers.clamp-function-closed-interval-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.lower-inverses-strictly-increasing-real-maps-proper-closed-intervals-real-numbers
open import real-numbers.maps-between-proper-closed-intervals-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-approximates-of-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-maps-proper-closed-intervals-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
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

Given a strictly increasing map `f : [a, b] → ℝ` and `y ∈ [f(a), f(b)]`, for any
`q r : ℚ` with `q < r`, then either:

1. `p < a`;
2. `b < q`;
3. `∃ (r s : ℚ) | (a < r < s < b) ∧ (p < r) ∧ (s < q)`.

If `p < a` (resp `b < q`) then `p` is in the lower cut of `f⁻¹(y)` (resp. `q` is
in the upper cut of `f⁻¹(y)`).

Otherwise, (3.) implies that `f r < f s`. By cotransitivity, then either:

- `f r < v` so `p` is in the lower cut of `f⁻¹(y)`;
- `v < f s` so `q` is in the upper cut of `f⁻¹(y)`.

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
          ( is-in-lower-cut-map-inv-le-lower-bound-is-strictly-increasing-real-map-proper-closed-interval-ℝ
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
            ( is-in-upper-cut-map-inv-le-upper-bound-is-strictly-increasing-real-map-proper-closed-interval-ℝ
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

### Interchange law for strict inequality

For any `x ∈ [a, b]` and `y ∈ [f(a), f(b)]`,

- `x < f⁻¹ y ⇒ f x < y`;
- `f⁻¹ y < x ⇒ y < f x`.

TODO: if `f` is ε-δ continuous at `x`, the converses hold.

```agda
module _
  { l l1 l2 : Level}
  ( I : proper-closed-interval-ℝ l1 l2)
  ( f : real-map-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) (l ⊔ l1 ⊔ l2) I)
  ( H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  ( x@(u , lo-bound-x , hi-bound-x) :
    type-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
  ( y@(v , lo-bound-y , hi-bound-y) :
    type-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)))
  where abstract opaque
    unfolding le-ℝ

    interchange-le-left-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      le-ℝ
        ( u)
        ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( y)) →
      le-ℝ (f x) v
    interchange-le-left-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      Kuy =
      let open do-syntax-trunc-Prop (le-prop-ℝ (f x) v)
      in do
        (q , hi-qu , lo-qy) ← Kuy
        (r , q<r , r<b , _) ← lo-qy

        concatenate-le-leq-ℝ
          ( f x)
          ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l q))
          ( v)
          ( H
            ( x)
            ( clamp-proper-closed-interval-ℝ I (raise-real-ℚ l q))
            ( preserves-le-left-sim-ℝ
              ( map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l q))
              ( map-clamp-proper-closed-interval-ℝ I u)
              ( u)
              ( clamp-is-in-closed-interval-ℝ
                ( closed-interval-proper-closed-interval-ℝ I)
                ( u)
                ( lo-bound-x , hi-bound-x))
              ( le-map-clamp-le-is-in-closed-interval-ℝ
                ( closed-interval-proper-closed-interval-ℝ I)
                ( u)
                ( lo-bound-x , hi-bound-x)
                ( raise-real-ℚ l q)
                ( ( transitive-leq-ℝ
                    ( lower-bound-proper-closed-interval-ℝ I)
                    ( u)
                    ( raise-real-ℚ l q)
                    ( preserves-leq-right-raise-ℝ l
                      { x = u}
                      { y = real-ℚ q}
                      ( leq-le-ℝ (le-real-is-in-upper-cut-ℝ u hi-qu)))
                    ( lo-bound-x)) ,
                  ( preserves-leq-left-raise-ℝ l
                    { x = real-ℚ q}
                    { y = upper-bound-proper-closed-interval-ℝ I}
                    ( leq-le-ℝ
                      ( transitive-le-ℝ
                        ( real-ℚ q)
                        ( real-ℚ r)
                        ( upper-bound-proper-closed-interval-ℝ I)
                        ( le-real-is-in-lower-cut-ℝ
                          ( upper-bound-proper-closed-interval-ℝ I)
                          ( r<b))
                        ( preserves-le-real-ℚ q<r)))))
                ( preserves-le-right-raise-ℝ l
                  { u}
                  { real-ℚ q}
                  ( le-real-is-in-upper-cut-ℝ u hi-qu)))))
          ( leq-map-is-in-lower-cut-map-inv-le-lower-bound-is-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( I)
            ( f)
            ( H)
            ( y)
            ( q)
            ( lo-qy))

    interchange-le-right-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      le-ℝ
        ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( y))
        ( u) →
      le-ℝ v (f x)
    interchange-le-right-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      Kyu =
      let open do-syntax-trunc-Prop (le-prop-ℝ v (f x))
      in do
        (q , hi-qy , lo-qu) ← Kyu
        (p , p<q , a<p , _) ← hi-qy

        concatenate-leq-le-ℝ
          ( v)
          ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l q))
          ( f x)
          ( leq-map-is-in-upper-cut-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( I)
            ( f)
            ( H)
            ( y)
            ( q)
            ( hi-qy))
          ( H
            ( clamp-proper-closed-interval-ℝ I (raise-real-ℚ l q))
            ( x)
            ( preserves-le-right-sim-ℝ
              ( map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l q))
              ( map-clamp-proper-closed-interval-ℝ I u)
              ( u)
              ( clamp-is-in-closed-interval-ℝ
                ( closed-interval-proper-closed-interval-ℝ I)
                ( u)
                ( lo-bound-x , hi-bound-x))
              ( le-map-clamp-le-is-in-closed-interval-ℝ
                ( closed-interval-proper-closed-interval-ℝ I)
                ( raise-real-ℚ l q)
                ( ( preserves-leq-right-raise-ℝ l
                    { x = lower-bound-proper-closed-interval-ℝ I}
                    { y = real-ℚ q}
                    ( leq-le-ℝ
                      ( transitive-le-ℝ
                        ( lower-bound-proper-closed-interval-ℝ I)
                        ( real-ℚ p)
                        ( real-ℚ q)
                        ( preserves-le-real-ℚ p<q)
                          ( le-real-is-in-upper-cut-ℝ
                          ( lower-bound-proper-closed-interval-ℝ I)
                        ( a<p))))) ,
                  ( transitive-leq-ℝ
                    ( raise-real-ℚ l q)
                    ( u)
                    ( upper-bound-proper-closed-interval-ℝ I)
                    ( hi-bound-x)
                    ( preserves-leq-left-raise-ℝ l
                      { x = real-ℚ q}
                      { y = u}
                      ( leq-le-ℝ (le-real-is-in-lower-cut-ℝ u lo-qu)))))
                ( u)
                ( lo-bound-x , hi-bound-x)
                ( preserves-le-left-raise-ℝ l
                  { real-ℚ q}
                  { u}
                  ( le-real-is-in-lower-cut-ℝ u lo-qu)))))

    interchange-le-right-is-ε-δ-continuous-map-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
      is-ε-δ-continuous-at-point-map-Metric-Space
        ( metric-space-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
        ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
        ( f)
        ( x) →
      le-ℝ (f x) v →
      le-ℝ
        ( u)
        ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( y))
    interchange-le-right-is-ε-δ-continuous-map-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      cont-f Hxv =
      let
        open
          do-syntax-trunc-Prop
            ( le-prop-ℝ
              ( u)
              ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                ( I)
                ( f)
                ( H)
                ( y)))
      in do
        ( ε , Hε) ←
          exists-ℚ⁺-in-lower-cut-is-positive-ℝ
            ( diff-ℝ v (f x))
            ( is-positive-diff-le-ℝ
              { x = f x}
              { y = v}
              ( Hxv))
        ( δ , Kδ) ← cont-f ε
        ( q , x<q , Nδxq) ← exists-rational-approximate-above-ℝ u δ
        ( p , p<q , x<p) ←
          forward-implication
            ( is-rounded-upper-cut-ℝ u q)
            ( x<q)
        ( p' , p'<p , x<p') ←
          forward-implication
            ( is-rounded-upper-cut-ℝ u p)
            ( x<p)
        let
          lemma-eq-clamp-x :
            clamp-proper-closed-interval-ℝ I u ＝ x
          lemma-eq-clamp-x =
            eq-type-subtype
              ( subtype-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
              ( eq-sim-ℝ
                ( clamp-is-in-closed-interval-ℝ
                  ( closed-interval-proper-closed-interval-ℝ I)
                  ( u)
                  ( (lo-bound-x , hi-bound-x))))

          lemma-Nfq :
            neighborhood-ℝ (l ⊔ l1 ⊔ l2) ε
              ( f x)
              ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l q))
          lemma-Nfq =
            Kδ
              ( clamp-proper-closed-interval-ℝ I (raise-real-ℚ l q))
              ( binary-tr
                ( neighborhood-Metric-Space
                  ( metric-space-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
                  ( δ))
                ( lemma-eq-clamp-x)
                ( eq-type-subtype
                  ( subtype-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
                  { clamp-proper-closed-interval-ℝ I
                    (raise-real-ℚ (l ⊔ l1 ⊔ l2) q)}
                  { clamp-proper-closed-interval-ℝ I
                    (raise-real-ℚ l q)}
                  ( eq-sim-ℝ
                    ( sim-clamp-closed-interval-ℝ
                      ( closed-interval-proper-closed-interval-ℝ I)
                      ( raise-real-ℚ (l ⊔ l1 ⊔ l2) q)
                      ( raise-real-ℚ l q)
                      ( sim-raise-raise-ℝ (l ⊔ l1 ⊔ l2) l (real-ℚ q)))))
                ( is-short-map-clamp-closed-interval-ℝ
                  ( closed-interval-proper-closed-interval-ℝ I)
                  ( δ)
                  ( u)
                  ( raise-real-ℚ (l ⊔ l1 ⊔ l2) q)
                  ( Nδxq)))

          lemma-leq-fq :
            leq-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l q))
              ( (f x) +ℝ (real-ℚ⁺ ε))
          lemma-leq-fq =
            leq-transpose-left-diff-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l q))
              ( real-ℚ⁺ ε)
              ( f x)
              ( swap-right-diff-leq-ℝ
                ( clamp-real-map-proper-closed-interval-ℝ I f
                  ( raise-real-ℚ l q))
                ( f x)
                ( real-ℚ⁺ ε)
                ( reversed-diff-bound-neighborhood-ℝ ε
                  ( f x)
                  ( clamp-real-map-proper-closed-interval-ℝ I f
                    ( raise-real-ℚ l q))
                  ( lemma-Nfq)))

          lemma-le-fq-y :
            le-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l q))
              ( v)
          lemma-le-fq-y =
            concatenate-leq-le-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l q))
              ( (f x) +ℝ (real-ℚ⁺ ε))
              ( v)
              ( lemma-leq-fq)
              ( le-transpose-right-diff-ℝ'
                ( real-ℚ⁺ ε)
                ( v)
                ( f x)
                ( le-real-is-in-lower-cut-ℝ (v -ℝ f x) Hε))

          lemma-lo-hi-p :
            is-in-lower-cut-ℝ
              ( upper-bound-proper-closed-interval-ℝ I)
              ( p)
          lemma-lo-hi-p =
            elim-disjunction
              ( lower-cut-ℝ (upper-bound-proper-closed-interval-ℝ I) p)
              ( id)
              ( λ hi-q →
                ex-falso
                  ( not-leq-le-ℝ
                    ( clamp-real-map-proper-closed-interval-ℝ I f
                      ( raise-real-ℚ l q))
                    ( v)
                  ( lemma-le-fq-y)
                  ( transitive-leq-ℝ
                    ( v)
                    ( f
                      ( raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
                        ( I)
                        ( l)))
                    ( clamp-real-map-proper-closed-interval-ℝ I f
                      ( raise-real-ℚ l q))
                    ( is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                      ( I)
                      ( f)
                      ( H)
                      ( _)
                      ( _)
                      ( preserves-leq-sim-ℝ
                        ( sim-raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
                          ( I)
                          ( l))
                        ( symmetric-sim-ℝ
                          ( clamp-leq-upper-bound-closed-interval-ℝ
                            ( closed-interval-proper-closed-interval-ℝ I)
                            ( raise-real-ℚ l q)
                            ( preserves-leq-right-raise-ℝ
                              ( l)
                              ( leq-le-ℝ
                                ( le-real-is-in-upper-cut-ℝ
                                  ( upper-bound-proper-closed-interval-ℝ I)
                                  ( hi-q))))))
                        ( refl-leq-ℝ _)))
                    ( hi-bound-y))))
              ( is-located-lower-upper-cut-ℝ
                ( upper-bound-proper-closed-interval-ℝ I)
                ( p<q))

          lemma-leq-fpv :
            leq-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l p))
              ( v)
          lemma-leq-fpv =
            transitive-leq-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l p))
              ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l q))
              ( v)
              ( leq-le-ℝ lemma-le-fq-y)
              ( is-increasing-map-clamp-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                ( I)
                ( f)
                ( H)
                ( _)
                ( _)
                ( leq-raise-leq-ℝ
                  ( l)
                  ( preserves-leq-real-ℚ (leq-le-ℚ p<q))))

        intro-exists p'
          ( x<p' , intro-exists p (p'<p , lemma-lo-hi-p , lemma-leq-fpv))

    -- interchange-le-left-is-ε-δ-continuous-map-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    --   is-ε-δ-continuous-at-point-map-Metric-Space
    --     ( metric-space-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
    --     ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
    --     ( f)
    --     ( x) →
    --   le-ℝ v (f x) →
    --   le-ℝ
    --     ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    --       ( I)
    --       ( f)
    --       ( H)
    --       ( y))
    --     ( u)
    -- interchange-le-left-is-ε-δ-continuous-map-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    --   cont-f Hvx =
    --   {!!}
```

### Interchange law for inequality

For any `x ∈ [a. b]` and `y ∈ [f(a), f(b)]`,

- `y ≤ f x ⇒ f⁻¹ y ≤ x`;
- `f x ≤ y ⇒ x ≤ f⁻¹ y`.

TODO: if `f` is ε-δ continuous at `x`, the converses hold.

```agda
module _
  { l l1 l2 : Level}
  ( I : proper-closed-interval-ℝ l1 l2)
  ( f : real-map-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) (l ⊔ l1 ⊔ l2) I)
  ( H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  ( x@(u , lo-bound-x , hi-bound-x) :
    type-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
  ( y@(v , lo-bound-y , hi-bound-y) :
    type-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)))
  where abstract

  interchange-leq-right-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    leq-ℝ v (f x) →
    leq-ℝ
      ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( y))
      ( u)
  interchange-leq-right-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    Kvx =
    leq-not-le-ℝ
      ( u)
      ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( y))
      ( map-neg
        ( interchange-le-left-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( x)
          ( y))
        ( not-le-leq-ℝ _ _ Kvx))

  interchange-leq-left-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    leq-ℝ (f x) v →
    leq-ℝ
      ( u)
      ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( y))
  interchange-leq-left-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    Kxv =
    leq-not-le-ℝ
      ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( y))
      ( u)
      ( map-neg
        ( interchange-le-right-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( x)
          ( y))
        ( not-le-leq-ℝ _ _ Kxv))
```

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
      is-in-lower-cut-map-inv-le-lower-bound-is-strictly-increasing-real-map-proper-closed-interval-ℝ
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
          is-in-upper-cut-map-inv-le-upper-bound-is-strictly-increasing-real-map-proper-closed-interval-ℝ
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

### The inverse function is increasing

```agda
module _
  { l l1 l2 : Level}
  ( I : proper-closed-interval-ℝ l1 l2)
  ( f : real-map-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) (l ⊔ l1 ⊔ l2) I)
  ( H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  ( y@(v , _ , _) y'@(v' , _ , _) :
    type-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)))
  ( y≤y' : leq-ℝ v v')
  where abstract opaque
  unfolding leq-ℝ

  preserves-leq-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    leq-ℝ
      ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( y))
      ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( y'))
  preserves-leq-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    q =
    map-tot-exists
      ( λ r (q<r , r<b , Hr) →
        ( ( q<r) ,
          ( r<b) ,
          ( transitive-leq-ℝ
            ( clamp-real-map-proper-closed-interval-ℝ I f (raise-real-ℚ l r))
            ( v)
            ( v')
            ( y≤y')
            ( Hr))))
```

### The inverse is a retraction

```agda
module _
  { l l1 l2 : Level}
  ( I : proper-closed-interval-ℝ l1 l2)
  ( f : real-map-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) (l ⊔ l1 ⊔ l2) I)
  ( H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where abstract

  leq-left-is-retraction-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    ( x@(u , _ , _) :
      type-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I) →
    leq-ℝ
      ( u)
      ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ I f H
        ( map-proper-closed-interval-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( x)))
  leq-left-is-retraction-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    x@(u , lo-bound , hi-bound) =
    interchange-leq-left-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( I)
      ( f)
      ( H)
      ( x)
      ( map-proper-closed-interval-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( x))
      ( refl-leq-ℝ (f x))

  leq-right-is-retraction-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    ( x@(u , _ , _) :
      type-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I) →
    leq-ℝ
      ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ I f H
        ( map-proper-closed-interval-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( x)))
      ( u)
  leq-right-is-retraction-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    x@(u , lo-bound , hi-bound) =
    interchange-leq-right-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( I)
      ( f)
      ( H)
      ( x)
      ( map-proper-closed-interval-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( x))
      ( refl-leq-ℝ (f x))

  is-retraction-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-retraction
      ( map-proper-closed-interval-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H))
      ( in-interval-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H))
  is-retraction-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    x =
    eq-type-subtype
      ( subtype-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
      ( antisymmetric-leq-ℝ _ _
        ( leq-right-is-retraction-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( x))
        ( leq-left-is-retraction-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( x)))
```

### The left inverse is surjective

```agda
module _
  { l l1 l2 : Level}
  ( I : proper-closed-interval-ℝ l1 l2)
  ( f : real-map-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) (l ⊔ l1 ⊔ l2) I)
  ( H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where abstract

  is-surjective-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-surjective
      ( in-interval-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H))
  is-surjective-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    =
    is-surjective-has-section
      ( ( map-proper-closed-interval-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)) ,
        ( is-retraction-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)))
```

### If the inverse is strictly increasing then it's an equivalence

```agda
module _
  { l l1 l2 : Level}
  ( I : proper-closed-interval-ℝ l1 l2)
  ( f : real-map-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) (l ⊔ l1 ⊔ l2) I)
  ( H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where abstract

  is-equiv-map-inv-is-strictly-increasing-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H))
      ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)) →
    is-equiv
      ( in-interval-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H))
  is-equiv-map-inv-is-strictly-increasing-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    K =
    is-equiv-is-emb-is-surjective
      ( is-surjective-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H))
      ( is-emb-is-injective
        ( is-set-type-subtype
          ( subtype-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
          ( is-set-ℝ _))
        ( λ {y} {y'} Hy →
          eq-type-subtype
            ( subtype-proper-closed-interval-ℝ
              ( l ⊔ l1 ⊔ l2)
              ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                ( I)
                ( f)
                ( H)))
            ( ap
              ( pr1)
              ( is-injective-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                  ( I)
                  ( f)
                  ( H))
                ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                  ( I)
                  ( f)
                  ( H))
                ( K)
                ( ap pr1 Hy)))))
```

### If the inverse is strictly increasing then the map is an equivalence

```agda
module _
  { l l1 l2 : Level}
  ( I : proper-closed-interval-ℝ l1 l2)
  ( f : real-map-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) (l ⊔ l1 ⊔ l2) I)
  ( H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where abstract

  is-equiv-map-is-strictly-increasing-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H))
      ( map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)) →
    is-equiv
      ( map-proper-closed-interval-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H))
  is-equiv-map-is-strictly-increasing-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    K =
    is-equiv-right-factor
      ( in-interval-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H))
      ( map-proper-closed-interval-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H))
      ( is-equiv-map-inv-is-strictly-increasing-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( K))
      ( is-equiv-htpy
        ( id)
        ( is-retraction-map-inv-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H))
        ( is-equiv-id))
```
