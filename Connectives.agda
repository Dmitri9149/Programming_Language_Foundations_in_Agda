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

-- Show sum is associative up to isomorphism.

to_assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C →  A ⊎ (B ⊎ C)
to_assoc (inj₁ (inj₁ x)) = inj₁ x
to_assoc (inj₂ x) = (inj₂ (inj₂ x))
to_assoc (inj₁ (inj₂ x)) = inj₂ (inj₁ x)

from_assoc : ∀ {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
from_assoc (inj₁ x) = (inj₁ (inj₁ x))
from_assoc (inj₂ (inj₂ x)) = inj₂ x
from_assoc (inj₂ (inj₁ x)) = (inj₁ (inj₂ x))

from_to_assoc : ∀ {A B C : Set} → (w : ((A ⊎ B) ⊎ C))
  → from_assoc (to_assoc w) ≡ w
from_to_assoc (inj₁ (inj₁ x)) = refl
from_to_assoc (inj₁ (inj₂ x)) = refl
from_to_assoc (inj₂ x) = refl

to_from_assoc : ∀ {A B C : Set} → (w : (A ⊎ (B ⊎ C)))
  → to_assoc (from_assoc w) ≡ w
to_from_assoc (inj₁ x) = refl
to_from_assoc (inj₂ (inj₁ x)) = refl
to_from_assoc (inj₂ (inj₂ x)) = refl

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to      = λ x → to_assoc x 
    ; from    = λ x → from_assoc x
    ; from∘to = λ x → from_to_assoc x
    ; to∘from = λ x → to_from_assoc x
    }

-- Show empty is the left identity of sums up to isomorphism.

data ⊥ : Set where

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A

⊥-elim ()

⊥-to : ∀ {A : Set} → ⊥ ⊎ A → A
⊥-to (inj₁ ())
⊥-to (inj₂ x) = x

⊥-from : ∀ {A : Set} → A → ⊥ ⊎ A 
⊥-from x = (inj₂ x)

⊥-from∘to : ∀ {A : Set} → (x : ⊥ ⊎ A)
  → inj₂ (⊥-to x) ≡ x
⊥-from∘to (inj₁ ())
⊥-from∘to (inj₂ x) = refl

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to      = λ x → ⊥-to x
    ; from    = λ x → ⊥-from x
    ; from∘to = λ x → ⊥-from∘to x
    ; to∘from = λ x → refl
    }

-- Show empty is the right identity of sums up to isomorphism.

postulate 
  ⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A

-- Show that the following property holds:
-- postulate
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , y ⟩ = inj₁ x 
⊎-weak-× ⟨ inj₂ x , y ⟩ = inj₂ ⟨ x , y ⟩


-- Show that a disjunct of conjuncts implies a conjunct of disjuncts:

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , y ⟩) = ⟨ inj₁ x , inj₁ y ⟩
⊎×-implies-×⊎ (inj₂ ⟨ x , y ⟩) = ⟨ inj₂ x , inj₂ y ⟩


