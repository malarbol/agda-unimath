# Euclidean division of integers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.euclidean-division-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.congruence-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.strict-inequality-integers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The Euclidean division of an integer `a` by a positive integer `d` is the pair
`(q , r) : ℤ × ℕ` such that `r < d` and `a = q d + r`.

## Definitions

### Euclidean division of an integer by a positive integer

```agda
module _
  (d : ℤ⁺) (a : ℤ)
  where

  fin-remainder-euclidean-division-ℤ : Fin (succ-ℕ (nat-positive-ℤ d))
  fin-remainder-euclidean-division-ℤ =
    mod-ℤ (succ-ℕ (nat-positive-ℤ d)) a

  nat-remainder-euclidean-division-ℤ : ℕ
  nat-remainder-euclidean-division-ℤ =
    nat-Fin (succ-ℕ (nat-positive-ℤ d)) fin-remainder-euclidean-division-ℤ

  int-remainder-euclidean-division-ℤ : ℤ
  int-remainder-euclidean-division-ℤ = int-ℕ nat-remainder-euclidean-division-ℤ

  cong-euclidean-division-ℤ :
    cong-ℤ (int-positive-ℤ d) (int-remainder-euclidean-division-ℤ) a
  cong-euclidean-division-ℤ =
    ( tr
      ( λ x → cong-ℤ x (int-remainder-euclidean-division-ℤ) a)
      ( eq-int-positive-succ-nat-positive-ℤ d)
      ( cong-int-mod-ℤ (succ-ℕ (nat-positive-ℤ d)) a))

  quotient-euclidean-division-ℤ : ℤ
  quotient-euclidean-division-ℤ =
    quotient-div-ℤ
      ( int-positive-ℤ d)
      ( a -ℤ int-remainder-euclidean-division-ℤ)
      ( symmetric-cong-ℤ
        ( int-positive-ℤ d)
        ( int-remainder-euclidean-division-ℤ)
        ( a)
        ( cong-euclidean-division-ℤ))

  abstract
    eq-diff-quotient-euclidean-diviion-ℤ :
      quotient-euclidean-division-ℤ *ℤ (int-positive-ℤ d) ＝
      a -ℤ int-remainder-euclidean-division-ℤ
    eq-diff-quotient-euclidean-diviion-ℤ =
      eq-quotient-div-ℤ
        ( int-positive-ℤ d)
        ( a -ℤ int-remainder-euclidean-division-ℤ)
        ( symmetric-cong-ℤ
          ( int-positive-ℤ d)
          ( int-remainder-euclidean-division-ℤ)
          ( a)
          ( cong-euclidean-division-ℤ))

    eq-euclidean-division-ℤ :
      add-ℤ
        ( quotient-euclidean-division-ℤ *ℤ int-positive-ℤ d)
        ( int-remainder-euclidean-division-ℤ) ＝
      ( a)
    eq-euclidean-division-ℤ =
      ( ap
        ( add-ℤ' int-remainder-euclidean-division-ℤ)
        ( eq-diff-quotient-euclidean-diviion-ℤ)) ∙
      ( is-section-right-add-neg-ℤ int-remainder-euclidean-division-ℤ a)

    strict-upper-bound-remainder-euclidean-division-ℤ :
      le-ℤ int-remainder-euclidean-division-ℤ (int-positive-ℤ d)
    strict-upper-bound-remainder-euclidean-division-ℤ =
      tr
        ( le-ℤ int-remainder-euclidean-division-ℤ)
        ( eq-int-positive-succ-nat-positive-ℤ d)
        ( le-natural-le-ℤ
          ( nat-remainder-euclidean-division-ℤ)
          ( succ-ℕ (nat-positive-ℤ d))
          ( strict-upper-bound-nat-Fin
            ( succ-ℕ (nat-positive-ℤ d))
            ( fin-remainder-euclidean-division-ℤ)))

  euclidean-division-ℤ :
    Σ ( ℕ)
      ( λ r →
        cong-ℤ (int-positive-ℤ d) (int-ℕ r) a ×
        le-ℤ (int-ℕ r) (int-positive-ℤ d))
  euclidean-division-ℤ =
    ( nat-remainder-euclidean-division-ℤ ,
      cong-euclidean-division-ℤ ,
      strict-upper-bound-remainder-euclidean-division-ℤ)
```

## Properties

### The Euclidean division of `a` by `d` locates `a` in an interval `q d ≤ a < (q + 1) d`

```agda
module _
  (d : ℤ⁺) (a : ℤ)
  where

  abstract
    locate-leq-left-euclidean-division-ℤ :
      leq-ℤ
        ( quotient-euclidean-division-ℤ d a *ℤ int-ℤ⁺ d)
        ( a)
    locate-leq-left-euclidean-division-ℤ =
      binary-tr
        ( leq-ℤ)
        ( right-unit-law-add-ℤ (quotient-euclidean-division-ℤ d a *ℤ int-ℤ⁺ d))
        ( eq-euclidean-division-ℤ d a)
        ( preserves-leq-right-add-ℤ
          ( quotient-euclidean-division-ℤ d a *ℤ int-ℤ⁺ d)
          ( zero-ℤ)
          ( int-remainder-euclidean-division-ℤ d a)
          ( leq-zero-int-ℕ (nat-remainder-euclidean-division-ℤ d a)))

    locate-le-right-euclidean-division-ℤ :
      le-ℤ
        ( a)
        ( succ-ℤ (quotient-euclidean-division-ℤ d a) *ℤ int-ℤ⁺ d)
    locate-le-right-euclidean-division-ℤ =
      binary-tr
        ( le-ℤ)
        ( eq-euclidean-division-ℤ d a)
        ( inv
          ( left-successor-law-mul-ℤ'
            ( quotient-euclidean-division-ℤ d a)
            ( int-ℤ⁺ d)))
        ( preserves-le-right-add-ℤ
          ( quotient-euclidean-division-ℤ d a *ℤ int-positive-ℤ d)
          ( int-remainder-euclidean-division-ℤ d a)
          ( int-ℤ⁺ d)
          ( strict-upper-bound-remainder-euclidean-division-ℤ d a))
```
