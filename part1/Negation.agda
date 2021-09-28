open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)

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

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

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

-- Show that conjunction, disjunction, and negation are related by a
-- version of De Morgan's Law.

--    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× {A} {B} = →-distrib-⊎ {A} {B} {⊥}

-- counter example
--  ¬ (⊥ × ⊥) ≃ ¬ ⊥ ≃ ⊥ → ⊥ ≃ ⊤
--  (¬ ⊥) ⊎ (¬ ⊥) ≃ (⊥ → ⊥) ⊎ (⊥ → ⊥) ≃ 2 × ⊤

{- 
Consider the following principles:

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.
-}





