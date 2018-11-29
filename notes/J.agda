-- Agda is an /interactive/ language;
-- that's very important difference (compared to language-pts)
module J where

open import Level
open import Data.Bool using (Bool; true; false)

data ⊤ : Set where
  I : ⊤

data ⊥ : Set where

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

Bool-elim : ∀ {ℓ} (P : Bool → Set ℓ) → P true → P false  → (b : Bool) → P b
Bool-elim P t f false = f
Bool-elim P t f true  = t

if1 : (r : Set1) → Bool → r → r → r
if1 r b t f = Bool-elim (λ _ → r) t f b

lemma-motive : Bool → Bool → Set
lemma-motive u v = if1 Set u (if1 Set v ⊤ ⊥) ⊤

lemma : Eq Bool true false → ⊥
lemma p = J Bool
  (λ u v _ → lemma-motive u v)
  (λ b → Bool-elim (λ c → lemma-motive c c) I I b )
  true false p
