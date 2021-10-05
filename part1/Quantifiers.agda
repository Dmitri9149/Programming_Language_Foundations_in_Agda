open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

∀-distrib-× : ∀ {A : Set} {B C : A → Set}
  → (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)

∀-distrib-× =
  record
    { to = λ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩
    ; from    = λ{ ⟨ f , g ⟩ → λ x → ⟨ f x , g x ⟩ }
    ; from∘to = λ f → refl
    ; to∘from = λ {⟨ f , g ⟩ → refl}
    } 


-- Show that a disjunction of universals implies a universal of disjunctions:

-- postulate
  -- ⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
    -- (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x

-- Does the converse hold? If so, prove; if not, explain why.

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

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x

⊎∀-implies-∀⊎ ( inj₁ f) = λ x → ( inj₁ (f x))
⊎∀-implies-∀⊎ ( inj₂ f) = λ x → ( inj₂ (f x))

{-
#### Exercise `∀-×` (practice)

Consider the following type.
```
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
```
Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.
Hint: you will need to postulate a version of extensionality that
works for dependent functions.
-}

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x) → f ≡ g

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

∀-× : {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc) 

∀-×-to : {B : Tri → Set} → (∀ (x : Tri) → B x) → (B aa × B bb × B cc)
∀-×-to = λ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩

∀-×-from : {B : Tri → Set} → (B aa × B bb × B cc) → (∀ (x : Tri) → B x)
∀-×-from = λ { (⟨ baa , ⟨ bbb , bcc ⟩ ⟩) →
  λ { aa → baa
    ; bb → bbb
    ; cc → bcc
    } 
  }

∀-×-from∘to : {B : Tri → Set} 
  → ∀ (f : (x : Tri) → B x ) → (∀-×-from ∘ ∀-×-to) f ≡ f
∀-×-from∘to = λ f → ∀-extensionality λ {aa → refl ; bb → refl; cc → refl}

∀-× {B} = record
  { to = ∀-×-to
  ; from = ∀-×-from
  ; from∘to = ∀-×-from∘to
  ; to∘from = λ y → refl
  }



