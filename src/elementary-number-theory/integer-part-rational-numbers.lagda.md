# The integer part of a rational number

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.integer-part-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.euclidean-division-integers
open import elementary-number-theory.inequality-integer-fractions
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-integers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

The {{concept "integer part" Disambiguation="rational number" Agda=int-part-ℚ}}
of a [rational number](elementary-number-theory.rational-numbers.md) `x : ℚ` is
the unique [integer](elementary-number-theory.integers.md) `k : ℕ` such that
`k ≤ x < k + 1`. It can be computed as the quotient of the
[Euclidean division](elementary-number-theory.euclidean-division-integers.md) of
its numerator by to its denominator.

## Definition

### The integer part of a rational number

```agda
int-part-ℚ : ℚ → ℤ
int-part-ℚ x =
  quotient-euclidean-division-ℤ
    ( positive-denominator-ℚ x)
    ( numerator-ℚ x)

rat-part-ℚ : ℚ → ℚ
rat-part-ℚ x = x -ℚ rational-ℤ (int-part-ℚ x)
```

## Property

### A rational number is greater than or equal to its integer part

TODO
