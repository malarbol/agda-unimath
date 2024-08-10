# The type of extended natural numbers

```agda
module elementary-number-theory.extended-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

The type of **extended natural numbers** is the type of downward stable subsets
of natural numbers. It naturally contains the set if natural numbers and an
additional point at infinity.

## Definitions

### The property of being downward stable

```agda
module _
  {l : Level}
  where

  is-downward-prop-subset-ℕ : (ℕ → Prop l) → Prop l
  is-downward-prop-subset-ℕ P =
    Π-Prop ℕ (λ (n : ℕ) → hom-Prop (P (succ-ℕ n)) (P n))

  is-downward-subset-ℕ : (ℕ → Prop l) → UU l
  is-downward-subset-ℕ P =
    type-Prop (is-downward-prop-subset-ℕ P)
```

### The type of extended natural numbers

```agda
ℕ∞ : (l : Level) → UU (lsuc l)
ℕ∞ l = type-subtype is-downward-prop-subset-ℕ

module _
  {l : Level} (α : ℕ∞ l)
  where

  subset-ℕ∞ : ℕ → Prop l
  subset-ℕ∞ = pr1 α

  seq-ℕ∞ : ℕ → UU l
  seq-ℕ∞ i = type-Prop (subset-ℕ∞ i)

  is-prop-seq-ℕ∞ : (i : ℕ) → is-prop (seq-ℕ∞ i)
  is-prop-seq-ℕ∞ i = is-prop-type-Prop (subset-ℕ∞ i)

  is-downward-subset-ℕ∞ : is-downward-subset-ℕ subset-ℕ∞
  is-downward-subset-ℕ∞ = pr2 α
```

## Properties

### A downward stable subset of the natural numbers is a lower subset

```agda
module _
  {l : Level} (α : ℕ → Prop l) (H : is-downward-subset-ℕ α)
  where

  is-order-reversing-is-downward-subset-ℕ :
    (n k : ℕ) → leq-ℕ n k → type-hom-Prop (α k) (α n)
  is-order-reversing-is-downward-subset-ℕ n =
    based-ind-ℕ
      ( n)
      ( λ k → type-hom-Prop (α k) (α n))
      ( λ K → K)
      ( λ k I J K → J (H k K))
```

### The underlying subset of an extended natural number is a lower set

```agda
module _
  {l : Level} (α : ℕ∞ l)
  where

  is-order-reversing-seq-ℕ∞ :
    (n k : ℕ) → leq-ℕ n k → type-hom-Prop (subset-ℕ∞ α k) (subset-ℕ∞ α n)
  is-order-reversing-seq-ℕ∞ =
    is-order-reversing-is-downward-subset-ℕ
      ( subset-ℕ∞ α)
      ( is-downward-subset-ℕ∞ α)
```

### Equality of extended natural numbers

```agda
module _
  {l : Level} (n m : ℕ∞ l)
  where

  eq-ℕ∞ : (subset-ℕ∞ n) ＝ (subset-ℕ∞ m) → n ＝ m
  eq-ℕ∞ = eq-type-subtype is-downward-prop-subset-ℕ
```

### The property of being an empty extended natural numbers

```agda
module _
  {l : Level} (α : ℕ∞ l)
  where

  is-empty-prop-ℕ∞ : Prop l
  is-empty-prop-ℕ∞ = Π-Prop ℕ (neg-Prop ∘ (subset-ℕ∞ α))

  is-empty-ℕ∞ : UU l
  is-empty-ℕ∞ = type-Prop is-empty-prop-ℕ∞
```

### An extended natural number is empty if and only if it has an empty head

```agda
module _
  {l : Level} (α : ℕ∞ l)
  where

  is-empty-head-is-empty-ℕ∞ : is-empty-ℕ∞ α → ¬ (seq-ℕ∞ α zero-ℕ)
  is-empty-head-is-empty-ℕ∞ H = H zero-ℕ

  is-empty-is-empty-head-ℕ∞ : ¬ (seq-ℕ∞ α zero-ℕ) → is-empty-ℕ∞ α
  is-empty-is-empty-head-ℕ∞ H n =
    H ∘ is-order-reversing-is-downward-subset-ℕ
      ( subset-ℕ∞ α)
      ( is-downward-subset-ℕ∞ α)
      ( zero-ℕ)
      ( n)
      ( leq-zero-ℕ n)
```

### The property of being a full extended natural numbers

```agda
module _
  {l : Level} (α : ℕ∞ l)
  where

  is-full-prop-ℕ∞ : Prop l
  is-full-prop-ℕ∞ = Π-Prop ℕ (subset-ℕ∞ α)

  is-full-ℕ∞ : UU l
  is-full-ℕ∞ = type-Prop is-full-prop-ℕ∞
```

### The successor and predecessor of an extended natural number

```agda
module _
  {l : Level} (α : ℕ∞ l)
  where

  succ-ℕ∞ : ℕ∞ l
  pr1 succ-ℕ∞ zero-ℕ = raise-unit-Prop l
  pr1 succ-ℕ∞ (succ-ℕ n) = subset-ℕ∞ α n
  pr2 succ-ℕ∞ zero-ℕ _ = raise-star
  pr2 succ-ℕ∞ (succ-ℕ n) I = is-downward-subset-ℕ∞ α n I

  pred-ℕ∞ : ℕ∞ l
  pr1 pred-ℕ∞ n = subset-ℕ∞ α (succ-ℕ n)
  pr2 pred-ℕ∞ n = is-downward-subset-ℕ∞ α (succ-ℕ n)
```

### The successor function on the extended natural numbers is a retracion

```agda
module _
  {l : Level}
  where

  eq-pred-succ-ℕ∞ : (α : ℕ∞ l) → α ＝ pred-ℕ∞ (succ-ℕ∞ α)
  eq-pred-succ-ℕ∞ α =
    eq-ℕ∞ α (pred-ℕ∞ (succ-ℕ∞ α)) refl
```

### The cannonical embedding from the natural numbers to the extended natural numbers

```agda
module _
  {l : Level} (n : ℕ)
  where

  extended-natural-ℕ : ℕ∞ l
  pr1 extended-natural-ℕ k = raise-Prop l (le-ℕ-Prop k n)
  pr2 extended-natural-ℕ k I =
    map-raise
      ( concatenate-leq-le-ℕ
        {k}
        {succ-ℕ k}
        {n}
        (succ-leq-ℕ k)
        (map-inv-raise I))

  inhabited-le-extended-natural-ℕ :
    (k : ℕ) → le-ℕ k n → seq-ℕ∞ extended-natural-ℕ k
  inhabited-le-extended-natural-ℕ k = map-raise

  empty-diagonal-extended-natural-ℕ : is-empty (seq-ℕ∞ extended-natural-ℕ n)
  empty-diagonal-extended-natural-ℕ = anti-reflexive-le-ℕ n ∘ map-inv-raise
```

### Zero in the extended natural numbers

```agda
module _
  {l : Level}
  where

  zero-ℕ∞ : ℕ∞ l
  zero-ℕ∞ = extended-natural-ℕ zero-ℕ

  is-empty-zero-ℕ∞ : is-empty-ℕ∞ zero-ℕ∞
  is-empty-zero-ℕ∞ k I = contradiction-le-zero-ℕ k (map-inv-raise I)
```

### Infinity in the extended natural numbers

```agda
module _
  {l : Level}
  where

  ∞-ℕ∞ : ℕ∞ l
  pr1 ∞-ℕ∞ m = raise-unit-Prop l
  pr2 ∞-ℕ∞ m I = I

  is-full-∞-ℕ∞ : is-full-ℕ∞ ∞-ℕ∞
  is-full-∞-ℕ∞ n = raise-star
```

### The double negation of an extended natural number

```agda
module _
  {l : Level} (α : ℕ∞ l)
  where

  ¬¬-ℕ∞ : ℕ∞ l
  pr1 ¬¬-ℕ∞ n = ¬¬' (subset-ℕ∞ α n)
  pr2 ¬¬-ℕ∞ n = map-double-negation (is-downward-subset-ℕ∞ α n)
```

### Inequality of extended natural numbers

```agda
module _
  {l : Level}
  where

  leq-prop-ℕ∞ : (m n : ℕ∞ l) → Prop l
  leq-prop-ℕ∞ m n = leq-prop-subtype (subset-ℕ∞ m) (subset-ℕ∞ n)

  leq-ℕ∞ : (m n : ℕ∞ l) → UU l
  leq-ℕ∞ m n = type-Prop (leq-prop-ℕ∞ m n)

  is-prop-leq-ℕ∞ : (m n : ℕ∞ l) → is-prop (leq-ℕ∞ m n)
  is-prop-leq-ℕ∞ m n = is-prop-type-Prop (leq-prop-ℕ∞ m n)
```

### Inequality of extended natural numbers is reflexive

```agda
  refl-leq-ℕ∞ : (n : ℕ∞ l) → leq-ℕ∞ n n
  refl-leq-ℕ∞ n = refl-leq-subtype (subset-ℕ∞ n)

  leq-eq-ℕ∞ : (m n : ℕ∞ l) → m ＝ n → leq-ℕ∞ m n
  leq-eq-ℕ∞ m .m refl = refl-leq-ℕ∞ m
```

### Inequality of extended natural numbers is transitive

```agda
  transitive-leq-ℕ∞ : (i j k : ℕ∞ l) → leq-ℕ∞ j k → leq-ℕ∞ i j → leq-ℕ∞ i k
  transitive-leq-ℕ∞ i j k =
    transitive-leq-subtype
      ( subset-ℕ∞ i)
      ( subset-ℕ∞ j)
      ( subset-ℕ∞ k)
```

### Inequality of extended natural numbers is antisymmetric

```agda
  antisymmetric-leq-ℕ∞ : (m n : ℕ∞ l) → leq-ℕ∞ m n → leq-ℕ∞ n m → m ＝ n
  antisymmetric-leq-ℕ∞ m n I J =
    eq-ℕ∞
      ( m)
      ( n)
      ( antisymmetric-leq-subtype (subset-ℕ∞ m) (subset-ℕ∞ n) I J)
```

### Zero is the minimal extended natural number

```agda
module _
  {l : Level} (α : ℕ∞ l)
  where

  leq-zero-ℕ∞ : leq-ℕ∞ zero-ℕ∞ α
  leq-zero-ℕ∞ k I = ex-falso (is-empty-zero-ℕ∞ k I)

  is-zero-leq-zero-ℕ∞ : leq-ℕ∞ α zero-ℕ∞ → α ＝ zero-ℕ∞
  is-zero-leq-zero-ℕ∞ H = antisymmetric-leq-ℕ∞ α zero-ℕ∞ H leq-zero-ℕ∞
```

### Zero is the only empty extended natural number

```agda
module _
  {l : Level} (α : ℕ∞ l)
  where

  leq-zero-is-empty-ℕ∞ : is-empty-ℕ∞ α → leq-ℕ∞ α zero-ℕ∞
  leq-zero-is-empty-ℕ∞ H n x = map-raise (H n x)

  is-zero-is-empty-ℕ∞ : is-empty-ℕ∞ α → α ＝ zero-ℕ∞
  is-zero-is-empty-ℕ∞ H =
    antisymmetric-leq-ℕ∞ α zero-ℕ∞ (leq-zero-is-empty-ℕ∞ H) (leq-zero-ℕ∞ α)
```

### Infinity is the maximal extended natural number

```agda
  leq-∞-ℕ∞ : leq-ℕ∞ α ∞-ℕ∞
  leq-∞-ℕ∞ k H = raise-star

  is-∞-leq-∞-ℕ∞ : leq-ℕ∞ ∞-ℕ∞ α → α ＝ ∞-ℕ∞
  is-∞-leq-∞-ℕ∞ H = antisymmetric-leq-ℕ∞ α ∞-ℕ∞ leq-∞-ℕ∞ H
```

### Infinity is the only full extended natural number

```agda
module _
  {l : Level} (α : ℕ∞ l) (H : is-full-ℕ∞ α)
  where

  leq-∞-is-full-ℕ∞ : leq-ℕ∞ ∞-ℕ∞ α
  leq-∞-is-full-ℕ∞ n K = H n

  is-∞-is-full-ℕ∞ : α ＝ ∞-ℕ∞
  is-∞-is-full-ℕ∞ = is-∞-leq-∞-ℕ∞ α leq-∞-is-full-ℕ∞
```

### No embedded natural number is equal to infinity

```agda
module _
  {l : Level} (n : ℕ)
  where

  not-leq-∞-extended-natural-ℕ : ¬ leq-ℕ∞ {l} ∞-ℕ∞ (extended-natural-ℕ n)
  not-leq-∞-extended-natural-ℕ H =
    empty-diagonal-extended-natural-ℕ n (H n raise-star)

  is-not-∞-extended-natural-ℕ : ∞-ℕ∞ ≠ (extended-natural-ℕ n)
  is-not-∞-extended-natural-ℕ =
    not-leq-∞-extended-natural-ℕ ∘ (leq-eq-ℕ∞ ∞-ℕ∞ (extended-natural-ℕ n))
```

### Any extended natural number greater than all natural numbers is infinite

```agda
module _
  {l : Level} (α : ℕ∞ l)
  where

  is-full-is-natural-upper-bound-ℕ∞ :
    ((n : ℕ) → leq-ℕ∞ (extended-natural-ℕ n) α) → is-full-ℕ∞ α
  is-full-is-natural-upper-bound-ℕ∞ H n =
    H (succ-ℕ n) n (map-raise (succ-le-ℕ n))

  is-∞-is-natural-upper-bound-ℕ∞ :
    ((n : ℕ) → leq-ℕ∞ (extended-natural-ℕ n) α) → α ＝ ∞-ℕ∞
  is-∞-is-natural-upper-bound-ℕ∞ =
    is-∞-is-full-ℕ∞ α ∘ is-full-is-natural-upper-bound-ℕ∞
```

### Any extended natural number is greater than its predecessor

```agda
module _
  {l : Level}
  where

  leq-pred-ℕ∞ : (α : ℕ∞ l) → leq-ℕ∞ (pred-ℕ∞ α) α
  leq-pred-ℕ∞ α = is-downward-subset-ℕ∞ α
```

### Any extended natural number is lesser than its successor

```agda
  leq-succ-ℕ∞ : (α : ℕ∞ l) → leq-ℕ∞ α (succ-ℕ∞ α)
  leq-succ-ℕ∞ α zero-ℕ H = raise-star
  leq-succ-ℕ∞ α (succ-ℕ n) H = is-downward-subset-ℕ∞ α n H
```

### The only extended natural number greater than its successor is infinity

```agda
module _
  {l : Level} (α : ℕ∞ l)
  where

  is-full-leq-succ-ℕ∞ : leq-ℕ∞ (succ-ℕ∞ α) α → is-full-ℕ∞ α
  is-full-leq-succ-ℕ∞ H zero-ℕ = H zero-ℕ raise-star
  is-full-leq-succ-ℕ∞ H (succ-ℕ k) = H (succ-ℕ k) (is-full-leq-succ-ℕ∞ H k)

  is-∞-leq-succ-ℕ∞ : leq-ℕ∞ (succ-ℕ∞ α) α → α ＝ ∞-ℕ∞
  is-∞-leq-succ-ℕ∞ = is-∞-is-full-ℕ∞ α ∘ is-full-leq-succ-ℕ∞
```

### Infinity is the only fix point of the successor function on the extended natural numbers

```agda
module _
  {l : Level}
  where

  has-fix-point-succ-ℕ∞ : succ-ℕ∞ {l} ∞-ℕ∞ ＝ ∞-ℕ∞
  has-fix-point-succ-ℕ∞ = is-∞-leq-∞-ℕ∞ (succ-ℕ∞ ∞-ℕ∞) (leq-succ-ℕ∞ ∞-ℕ∞)

  is-∞-is-fix-point-succ-ℕ∞ : (α : ℕ∞ l) → succ-ℕ∞ α ＝ α → α ＝ ∞-ℕ∞
  is-∞-is-fix-point-succ-ℕ∞ α = is-∞-leq-succ-ℕ∞ α ∘ leq-eq-ℕ∞ (succ-ℕ∞ α) α
```

### Any extended natural number is lesser than the successor of its predecessor

```agda
module _
  {l : Level}
  where

  leq-succ-pred-ℕ∞ : (α : ℕ∞ l) → leq-ℕ∞ α (succ-ℕ∞ (pred-ℕ∞ α))
  leq-succ-pred-ℕ∞ α zero-ℕ H = raise-star
  leq-succ-pred-ℕ∞ α (succ-ℕ k) H = H
```

### An extended natural number is lesser than its double negation

```agda
module _
  {l : Level}
  where

  leq-¬¬-ℕ∞ : (α : ℕ∞ l) → leq-ℕ∞ α (¬¬-ℕ∞ α)
  leq-¬¬-ℕ∞ α n = intro-double-negation
```

### The double negation of infinity is itself

```agda
module _
  {l : Level}
  where

  eq-¬¬-∞-ℕ∞ : ¬¬-ℕ∞ {l} ∞-ℕ∞ ＝ ∞-ℕ∞
  eq-¬¬-∞-ℕ∞ = is-∞-leq-∞-ℕ∞ (¬¬-ℕ∞ ∞-ℕ∞) (leq-¬¬-ℕ∞ ∞-ℕ∞)
```

### The double negation of a natural number is itself

```agda
module _
  {l : Level} (n : ℕ)
  where

  leq-¬¬-extended-natural-ℕ :
    leq-ℕ∞ {l} (¬¬-ℕ∞ (extended-natural-ℕ n)) (extended-natural-ℕ n)
  leq-¬¬-extended-natural-ℕ k H =
    rec-coproduct
      ( map-raise)
      ( ex-falso ∘ H ∘ map-neg map-inv-raise)
      ( is-decidable-le-ℕ k n)

  eq-¬¬-extended-natural-ℕ :
    ¬¬-ℕ∞ {l} (extended-natural-ℕ n) ＝ extended-natural-ℕ n
  eq-¬¬-extended-natural-ℕ =
    antisymmetric-leq-ℕ∞
      ( ¬¬-ℕ∞ (extended-natural-ℕ n))
      ( extended-natural-ℕ n)
      ( leq-¬¬-extended-natural-ℕ)
      ( leq-¬¬-ℕ∞ (extended-natural-ℕ n))
```

### The double negation preserves inequality

```agda
module _
  {l : Level} (α β : ℕ∞ l)
  where

  preserves-leq-¬¬-ℕ∞ : leq-ℕ∞ α β → leq-ℕ∞ (¬¬-ℕ∞ α) (¬¬-ℕ∞ β)
  preserves-leq-¬¬-ℕ∞ H = map-double-negation ∘ H
```

### The double negation is idempotent

```agda
module _
  {l : Level} (α : ℕ∞ l)
  where

  leq-double-¬¬-ℕ∞ : leq-ℕ∞ (¬¬-ℕ∞ (¬¬-ℕ∞ α)) (¬¬-ℕ∞ α)
  leq-double-¬¬-ℕ∞ = double-negation-elim-neg ∘ ¬_ ∘ (seq-ℕ∞ α)

  idempotent-¬¬-ℕ∞ : (¬¬-ℕ∞ (¬¬-ℕ∞ α)) ＝ (¬¬-ℕ∞ α)
  idempotent-¬¬-ℕ∞ =
    antisymmetric-leq-ℕ∞
      ( ¬¬-ℕ∞ (¬¬-ℕ∞ α))
      ( ¬¬-ℕ∞ α)
      ( leq-double-¬¬-ℕ∞)
      ( leq-¬¬-ℕ∞ (¬¬-ℕ∞ α))
```

### The cannonical inclusion of natural numbers preserves and reflects inequality

```agda
module _
  {l : Level} (i j : ℕ)
  where

  preserves-leq-extended-natural-ℕ :
    leq-ℕ i j → leq-ℕ∞ {l} (extended-natural-ℕ i) (extended-natural-ℕ j)
  preserves-leq-extended-natural-ℕ H k K =
    map-raise (concatenate-le-leq-ℕ {k} {i} {j} (map-inv-raise K) H)

  reflects-leq-extended-natural-ℕ :
    leq-ℕ∞ {l} (extended-natural-ℕ i) (extended-natural-ℕ j) → leq-ℕ i j
  reflects-leq-extended-natural-ℕ H =
    rec-coproduct
      ( λ I →
        ex-falso
          ( empty-diagonal-extended-natural-ℕ
            ( j)
            ( H j (map-raise I))))
      ( leq-not-le-ℕ j i)
      ( is-decidable-le-ℕ j i)
```

### The cannonical inclusion of natural numbers is injective

```agda
module _
  {l : Level}
  where

  is-injective-extended-natural-ℕ : is-injective (extended-natural-ℕ {l})
  is-injective-extended-natural-ℕ {i} {j} H =
    antisymmetric-leq-ℕ
      ( i)
      ( j)
      ( reflects-leq-extended-natural-ℕ
        ( i)
        ( j)
        ( leq-eq-ℕ∞ (extended-natural-ℕ i) (extended-natural-ℕ j) H))
      ( reflects-leq-extended-natural-ℕ
        ( j)
        ( i)
        ( leq-eq-ℕ∞ (extended-natural-ℕ j) (extended-natural-ℕ i) (inv H)))
```

### An extended natural number `α` is lesser than `n` if and only if `α n` is empty

```agda
module _
  {l : Level} (α : ℕ∞ l) (n : ℕ)
  where

  leq-is-empty-seq-ℕ∞ :
    ¬ (seq-ℕ∞ α n) → leq-ℕ∞ α (extended-natural-ℕ n)
  leq-is-empty-seq-ℕ∞ H k K =
    rec-coproduct
      ( map-raise)
      ( λ I →
        ex-falso
          (H (is-order-reversing-seq-ℕ∞ α n k (leq-not-le-ℕ k n I) K)))
      ( is-decidable-le-ℕ k n)

  is-empty-seq-leq-ℕ∞ :
    leq-ℕ∞ α (extended-natural-ℕ n) → ¬ (seq-ℕ∞ α n)
  is-empty-seq-leq-ℕ∞ H K =
    empty-diagonal-extended-natural-ℕ n (H n K)
```

### An extended natural number `α` is greater than `succ-ℕ n` if and only if `α n` is inhabited

```agda
module _
  {l : Level} (n : ℕ) (α : ℕ∞ l)
  where

  leq-succ-is-inhabited-seq-ℕ∞ :
    seq-ℕ∞ α n → leq-ℕ∞ (extended-natural-ℕ (succ-ℕ n)) α
  leq-succ-is-inhabited-seq-ℕ∞ H k I =
    is-order-reversing-seq-ℕ∞
      ( α)
      ( k)
      ( n)
      ( leq-le-succ-ℕ k n (map-inv-raise I))
      ( H)

  is-inhabited-seq-leq-succ-ℕ∞ :
    leq-ℕ∞ (extended-natural-ℕ (succ-ℕ n)) α → seq-ℕ∞ α n
  is-inhabited-seq-leq-succ-ℕ∞ H = H n (map-raise (succ-le-ℕ n))
```

```agda
module _
  {l : Level} (α : ℕ∞ l) (n : ℕ)
  where

  not-leq-succ-leq-ℕ∞ :
    leq-ℕ∞ α (extended-natural-ℕ n) →
    ¬ (leq-ℕ∞ (extended-natural-ℕ (succ-ℕ n)) α)
  not-leq-succ-leq-ℕ∞ H =
    is-empty-seq-leq-ℕ∞ α n H ∘ is-inhabited-seq-leq-succ-ℕ∞ n α

  leq-not-leq-succ-ℕ∞ :
    ¬ (leq-ℕ∞ (extended-natural-ℕ (succ-ℕ n)) α) →
    leq-ℕ∞ α (extended-natural-ℕ n)
  leq-not-leq-succ-ℕ∞ =
    leq-is-empty-seq-ℕ∞ α n ∘ map-neg (leq-succ-is-inhabited-seq-ℕ∞ n α)

  not-leq-leq-succ-ℕ∞ :
    leq-ℕ∞ (extended-natural-ℕ (succ-ℕ n)) α → ¬ leq-ℕ∞ α (extended-natural-ℕ n)
  not-leq-leq-succ-ℕ∞ =
    map-neg (is-empty-seq-leq-ℕ∞ α n) ∘
    intro-double-negation ∘
    is-inhabited-seq-leq-succ-ℕ∞ n α

  elim-double-negationl-leq-ℕ∞ :
    ¬¬ leq-ℕ∞ α (extended-natural-ℕ n) → leq-ℕ∞ α (extended-natural-ℕ n)
  elim-double-negationl-leq-ℕ∞ =
    leq-not-leq-succ-ℕ∞ ∘ map-neg not-leq-leq-succ-ℕ∞
```

### The cannonical inclusion of natural numbers commutes with the successor functions

```agda
module _
  {l : Level} (n : ℕ)
  where

  leq-extended-natural-succ-ℕ :
    leq-ℕ∞ (extended-natural-ℕ {l} (succ-ℕ n)) (succ-ℕ∞ (extended-natural-ℕ n))
  leq-extended-natural-succ-ℕ zero-ℕ x = x
  leq-extended-natural-succ-ℕ (succ-ℕ k) x = x

  leq-succ-extended-natural-ℕ :
    leq-ℕ∞ (succ-ℕ∞ (extended-natural-ℕ n)) (extended-natural-ℕ {l} (succ-ℕ n))
  leq-succ-extended-natural-ℕ zero-ℕ x = x
  leq-succ-extended-natural-ℕ (succ-ℕ k) x = x

  preserves-succ-extended-natural-ℕ :
    extended-natural-ℕ {l} (succ-ℕ n) ＝ succ-ℕ∞ (extended-natural-ℕ n)
  preserves-succ-extended-natural-ℕ =
    antisymmetric-leq-ℕ∞
      ( extended-natural-ℕ {l} (succ-ℕ n))
      ( succ-ℕ∞ (extended-natural-ℕ n))
      ( leq-extended-natural-succ-ℕ)
      ( leq-succ-extended-natural-ℕ)
```

```agda
module _
  {l : Level} (α : ℕ∞ l)
  where

  lower-subset-natural-ℕ∞ : ℕ → Prop l
  lower-subset-natural-ℕ∞ k = leq-prop-ℕ∞ (extended-natural-ℕ k) α

  is-downward-lower-subset-natural-ℕ∞ :
    is-downward-subset-ℕ lower-subset-natural-ℕ∞
  is-downward-lower-subset-natural-ℕ∞ n I =
    transitive-leq-ℕ∞
      ( extended-natural-ℕ n)
      ( extended-natural-ℕ (succ-ℕ n))
      ( α)
      ( I)
      ( preserves-leq-extended-natural-ℕ
        ( n)
        ( succ-ℕ n)
        ( succ-leq-ℕ n))
```

### The cannonical retraction from subsets of natural numbers to extended natural numbers

```agda
module _
  {l : Level} (P : ℕ → Prop l)
  where

  downward-subset-ℕ : ℕ → Prop l
  downward-subset-ℕ n = Π-Prop ℕ (λ k → hom-Prop (leq-ℕ-Prop k n) (P k))

  is-downward-downward-subset-ℕ : is-downward-subset-ℕ downward-subset-ℕ
  is-downward-downward-subset-ℕ n H k =
    H k ∘ transitive-leq-ℕ k n (succ-ℕ n) (succ-leq-ℕ n)

  leq-downward-subset-ℕ : downward-subset-ℕ ⊆ P
  leq-downward-subset-ℕ n H = H n (refl-leq-ℕ n)

  leq-downward-is-downward-subset-ℕ :
    is-downward-subset-ℕ P → P ⊆ downward-subset-ℕ
  leq-downward-is-downward-subset-ℕ H n I k J =
    is-order-reversing-is-downward-subset-ℕ P H k n J I

  extended-natural-subset-ℕ : ℕ∞ l
  extended-natural-subset-ℕ =
    (downward-subset-ℕ , is-downward-downward-subset-ℕ)

  lemma-downward-subset-succ-ℕ :
    (n : ℕ) (H : type-Prop (downward-subset-ℕ n)) →
    (K : type-Prop (P (succ-ℕ n))) →
    type-Prop (downward-subset-ℕ (succ-ℕ n))
  lemma-downward-subset-succ-ℕ n H K k I =
    rec-coproduct
      ( H k)
      ( λ J → inv-tr (type-Prop ∘ P) J K)
      ( decide-leq-succ-ℕ k n I)
```

### The cannonical retraction from subsets of natural numbers to extended natural numbers is idempotent

```agda
module _
  {l : Level} (P : ℕ → Prop l)
  where

  idempotent-downward-subset-ℕ :
    Id
      ( downward-subset-ℕ P)
      ( downward-subset-ℕ (downward-subset-ℕ P))
  idempotent-downward-subset-ℕ =
    antisymmetric-leq-subtype
      ( downward-subset-ℕ P)
      ( downward-subset-ℕ (downward-subset-ℕ P))
      ( leq-downward-is-downward-subset-ℕ
        ( downward-subset-ℕ P)
        ( is-downward-downward-subset-ℕ P))
      ( leq-downward-subset-ℕ (downward-subset-ℕ P))
```

### Any extended natural number is the extended natural subset of itself

```agda
module _
  {l : Level}
  where

  is-retract-extended-natural-subset-ℕ∞ :
    (α : ℕ∞ l) → α ＝ extended-natural-subset-ℕ (subset-ℕ∞ α)
  is-retract-extended-natural-subset-ℕ∞ α =
    eq-ℕ∞
      ( α)
      ( extended-natural-subset-ℕ (subset-ℕ∞ α))
      ( antisymmetric-leq-subtype
        ( subset-ℕ∞ α)
        ( downward-subset-ℕ (subset-ℕ∞ α))
        ( leq-downward-is-downward-subset-ℕ
          ( subset-ℕ∞ α)
          ( is-downward-subset-ℕ∞ α))
        ( leq-downward-subset-ℕ (subset-ℕ∞ α)))
```

## See also

- [Infinite sets that satisfy the principle of omniscience in all varieties of constructive mathematics](https://www.cs.bham.ac.uk/~mhe/papers/omniscient-2011-07-06.pdf)
