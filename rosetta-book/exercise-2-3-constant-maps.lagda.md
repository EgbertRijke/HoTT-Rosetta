# Exercise 2.3

```agda
module exercise-2-3-constant-maps where

open import universe-levels
```

## Problem statement

### Exercise 2.3(a)

Construct the **constant map**

```text
           Γ ⊢ A type
  ----------------------------
   Γ, y : B ⊢ const_y : A → B
```

### Exercise 2.3(b)

Show that

```text
                 Γ ⊢ f : A → B
  ------------------------------------------
   Γ, z : C ⊢ const_z ∘ f ≐ const_z : A → C
```

### Exercise 2.3(c)

Show that

```text
           Γ ⊢ A type   Γ ⊢ g : B → C
  -----------------------------------------------
   Γ, y : B ⊢ g ∘ const_y ≐ const_{g(y)} : A → C
```

## Solution

```agda
const : {l1 l2 : Level} (A : UU l1) {B : UU l2} → B → A → B
const A b x = b
```

## Supplement

### The diagonal

```agda
module _
  {l1 l2 : Level} (A : UU l1) (X : UU l2)
  where

  diagonal-exponential : A → X → A
  diagonal-exponential = const X
```
