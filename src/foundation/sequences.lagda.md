# Sequences

```agda
module foundation.sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-sequences
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

A **sequence** of elements in a type `A` is a map `ℕ → A`.

## Definition

### Sequences of elements of a type

```agda
sequence : {l : Level} → UU l → UU l
sequence A = dependent-sequence (λ _ → A)
```

### Functorial action on maps of sequences

```agda
map-sequence :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → sequence A → sequence B
map-sequence f a = f ∘ a
```

### The equivalence relation of being asymptotically equal sequences

#### The relation of being asymptotically equal sequences

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A)
  where

  is-modulus-eq-∞-sequence : ℕ → UU l
  is-modulus-eq-∞-sequence N =
    (m : ℕ) → leq-ℕ N m → u m ＝ v m

  eq-∞-sequence : UU l
  eq-∞-sequence = Σ ℕ is-modulus-eq-∞-sequence
```

#### Any sequence is asymptotically equal to itself

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  refl-eq-∞-sequence : eq-∞-sequence u u
  pr1 refl-eq-∞-sequence = zero-ℕ
  pr2 refl-eq-∞-sequence m H = refl
```

#### Being asymptotically equal is a symmetric relation

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A)
  where

  symmetric-eq-∞-sequence : eq-∞-sequence u v → eq-∞-sequence v u
  symmetric-eq-∞-sequence =
    map-Σ
      ( is-modulus-eq-∞-sequence v u)
      ( id)
      ( λ N H m K → inv (H m K))
```

#### Being asymptotically equal is a transitive relation

```agda
module _
  {l : Level} {A : UU l} (u v w : sequence A)
  where

  is-modulus-max-modulus-eq-∞-sequence :
    (m n : ℕ) →
    is-modulus-eq-∞-sequence v w n →
    is-modulus-eq-∞-sequence u v m →
    is-modulus-eq-∞-sequence u w (max-ℕ m n)
  is-modulus-max-modulus-eq-∞-sequence m n H K p I =
    ( K p (leq-left-leq-max-ℕ p m n I)) ∙
    ( H p (leq-right-leq-max-ℕ p m n I))

  transitive-eq-∞-sequence :
    eq-∞-sequence v w →
    eq-∞-sequence u v →
    eq-∞-sequence u w
  transitive-eq-∞-sequence (n , H) (m , K) =
    (max-ℕ m n , is-modulus-max-modulus-eq-∞-sequence m n H K)
```

## Properties

### Asymptotically constant sequences

#### Asymptotical values

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (x : A)
  where

  is-modulus-asymptotical-value : (N : ℕ) → UU l
  is-modulus-asymptotical-value N = (n : ℕ) → (leq-ℕ N n) → x ＝ u n

  is-asymptotical-value : UU l
  is-asymptotical-value = Σ ℕ is-modulus-asymptotical-value

  modulus-asymptotical-value : is-asymptotical-value → ℕ
  modulus-asymptotical-value H = pr1 H

  is-modulus-modulus-asymptotical-value :
    (H : is-asymptotical-value) →
    is-modulus-asymptotical-value (modulus-asymptotical-value H)
  is-modulus-modulus-asymptotical-value H = pr2 H
```

#### The asymptotical value of a sequence is unique

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  eq-asymptotical-value :
    (x y : A) →
    is-asymptotical-value u x →
    is-asymptotical-value u y →
    x ＝ y
  eq-asymptotical-value x y H K = α ∙ (inv β)
    where

    N : ℕ
    N =
      max-ℕ
        ( modulus-asymptotical-value u x H)
        ( modulus-asymptotical-value u y K)

    α : x ＝ u N
    α =
      is-modulus-modulus-asymptotical-value u x H N
        ( leq-left-leq-max-ℕ N
          ( modulus-asymptotical-value u x H)
          ( modulus-asymptotical-value u y K)
          ( refl-leq-ℕ N))

    β : y ＝ u N
    β =
      is-modulus-modulus-asymptotical-value u y K N
        ( leq-right-leq-max-ℕ N
          ( modulus-asymptotical-value u x H)
          ( modulus-asymptotical-value u y K)
          ( refl-leq-ℕ N))

  is-asymptotically-constant : UU l
  is-asymptotically-constant = Σ A (is-asymptotical-value u)
```

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (H : is-asymptotically-constant u)
  where

  ∞-value-∞-constant-sequence : A
  ∞-value-∞-constant-sequence = pr1 H

  ∞-eq-∞-constant-sequence : eq-∞-sequence (λ n → ∞-value-∞-constant-sequence) u
  ∞-eq-∞-constant-sequence = pr2 H

  modulus-∞-constant-sequence : ℕ
  modulus-∞-constant-sequence = pr1 ∞-eq-∞-constant-sequence

  is-modulus-modulus-∞-constant-sequence :
    is-modulus-asymptotical-value u
      ∞-value-∞-constant-sequence
      modulus-∞-constant-sequence
  is-modulus-modulus-∞-constant-sequence = pr2 ∞-eq-∞-constant-sequence
```
