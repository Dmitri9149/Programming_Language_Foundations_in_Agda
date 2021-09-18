import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g


infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

postulate 
  ≃-refl : ∀ {A : Set} → A ≃ A

  ≃-trans : ∀ {A B C : Set}
    → A ≃ B
    → B ≃ C
  -----
    → A ≃ C

-- Show that `A ⇔ B` as defined [earlier](/Isomorphism/#iff)
-- is isomorphic to `(A → B) × (B → A)`.


infix 1 _⇔_
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_

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

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ ((A → B) × (B → A))

⇔≃× = 
  record 
    { to = λ x → ⟨ _⇔_.to x , _⇔_.from x ⟩
    ; from = λ x → record { to = proj₁ x ; from = proj₂ x }
    ; from∘to = λ x → refl
    ; to∘from = λ x → η-× x
    }


-- Show sum is commutative up to isomorphism.

data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

⊎-swap : ∀ {A B : Set} → A ⊎ B → B ⊎ A
⊎-swap (inj₁ a) = inj₂ a
⊎-swap (inj₂ b) = inj₁ b

⊎-swap_swap : ∀ {A B : Set} → (w : A ⊎ B)
  → ⊎-swap (⊎-swap w) ≡ w
⊎-swap_swap (inj₁ a) = refl
⊎-swap_swap (inj₂ b) = refl

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to      = λ x → ⊎-swap x
    ; from    = λ y → ⊎-swap y
    ; from∘to = λ x → ⊎-swap_swap x
    ; to∘from = λ y → ⊎-swap_swap y
    }



