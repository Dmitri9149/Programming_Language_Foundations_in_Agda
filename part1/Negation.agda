open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive zero ()
<-irreflexive (suc n) (s<s n<n) = <-irreflexive n n<n

-- ...for any naturals `m` and `n` exactly one of the following holds:

--  `m < n`
--  `m ≡ n`
--  `m > n`

-- Here "exactly one" means that not only one of the three must hold,
-- but that when one holds the negation of the other two must also hold.

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

data Trichotomy (m n : ℕ) : Set where
  up : m < n → ¬ (m ≡ n) → ¬ (n < m) → Trichotomy m n
  down : n < m → ¬ (m ≡ n) → ¬ (m < n) → Trichotomy m n
  equal : m ≡ n → ¬ (m < n) → ¬ (n < m) → Trichotomy m n

suc-≡ : ∀ { m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-≡ refl = refl

suc-< : ∀ {m n : ℕ} → suc m < suc n → m < n
suc-< (s<s m<n) = m<n


trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero zero = equal refl (λ ()) (λ ())
trichotomy zero (suc n) = up z<s (λ ()) (λ ())
trichotomy (suc m) (zero) = down z<s (λ ()) (λ ())
trichotomy (suc m) (suc n) with trichotomy m n
... | up l e g = up (s<s l) (e ∘ suc-≡) (g ∘ suc-<)
... | down g e l = down (s<s g) (e ∘ suc-≡) (l ∘ suc-<) 
... | equal e l g = equal (cong suc e) (l ∘ suc-<) (g ∘ suc-<)

