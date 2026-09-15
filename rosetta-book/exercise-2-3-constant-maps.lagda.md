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
const : {l1 l2 : Level} (A : Type l1) {B : Type l2} → B → A → B
const A b x = b
```
