-- Agda is an /interactive/ language;
-- that's very important difference (compared to language-pts)
module J where

open import Level

data Eq {ℓ : Level} (A : Set ℓ) : A → A → Set ℓ where
    refl : {x : A} → Eq A x x

J : ∀ {ℓ ℓ′} (A : Set ℓ)
  → (C : (x : A) → (y : A) → (p : Eq A x y) → Set ℓ′)
  → (r : (x : A) → C x x refl)
  → (u : A)
  → (v : A)
  → (p : Eq A u v)
  → C u v p
J A C r u .u refl = r u

Eq-sym : ∀ {ℓ} (A : Set ℓ) (x y : A) → Eq A x y → Eq A y x
Eq-sym A x .x refl = refl

Eq-sym-with-J : ∀ {ℓ} (A : Set ℓ) (x y : A) → Eq A x y → Eq A y x
Eq-sym-with-J A = J A (λ x y _ → Eq A y x) (λ x → refl)

Eq-trans-with-J : ∀ {ℓ} (A : Set ℓ) (x y z : A) → Eq A x y → Eq A y z → Eq A x z
Eq-trans-with-J A x y z p = J A (λ u v _ → Eq A v z → Eq A u z) (λ _ r → r) x y p
