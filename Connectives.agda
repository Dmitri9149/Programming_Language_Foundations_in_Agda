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
