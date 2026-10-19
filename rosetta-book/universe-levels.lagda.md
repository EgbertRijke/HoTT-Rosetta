# Universe levels

```agda
module universe-levels where

open import Agda.Primitive
  using (Level ; lzero ; lsuc ; _⊔_)
  renaming (Set to UU ; Setω to UUω)
  public

data raise (l : Level) {l1 : Level} (A : UU l1) : UU (l1 ⊔ l) where
  map-raise : A → raise l A
```
