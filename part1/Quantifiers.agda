open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

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
{- 
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
-}

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

-------------
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

-- Show that existentials distribute over disjunction:
{--
postulate
  ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
-}

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)

∃-distrib-⊎ =
  record
    { to  = λ{ ⟨ x , (inj₁ b) ⟩ → inj₁ ⟨ x , b ⟩ ; ⟨ x , (inj₂ c) ⟩ → inj₂ ⟨ x , c ⟩ }
    ; from  = λ{ (inj₁ ⟨ x , b ⟩) → ⟨ x , (inj₁ b) ⟩ ; (inj₂ ⟨ x , c ⟩) → ⟨ x , (inj₂ c) ⟩ }
    ; from∘to = λ{ ⟨ x , (inj₁ b) ⟩ → refl ; ⟨ x , (inj₂ c) ⟩ → refl }
    ; to∘from = λ{ (inj₁ ⟨ x , b ⟩) → refl ; (inj₂ ⟨ x , c ⟩) → refl }
    }

{-
Show that an existential of conjunctions implies a conjunction of existentials:
postulate
  ∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
-}


∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)

∃×-implies-×∃ ⟨ x , ⟨ b , c ⟩ ⟩ = ⟨ ⟨ x , b ⟩ , ⟨ x , c ⟩ ⟩

-- ×∃-implies-∃× : ∀ {A : Set} {B C : A → Set} → (∃[ x ] B x) × (∃[ x ] C x) → ∃[ x ] (B x × C x)
-- ×∃-implies-∃× ⟨ ⟨ x , b ⟩ , ⟨ y , c ⟩ ⟩ = ⟨ x , ⟨ b , c ⟩ ⟩
-- ×∃-implies-∃× ⟨ ⟨ x , b ⟩ , ⟨ y , c ⟩ ⟩ = ⟨ y , ⟨ b , c ⟩ ⟩


-- Let Tri and B be as in Exercise ∀-×. Show that ∃[ x ] B x is isomorphic to B aa ⊎ B bb ⊎ B cc.
∃-⊎ : {B : Tri → Set} → (∃[ x ] B x) ≃ (B aa  ⊎ B bb ⊎ B cc)

∃-⊎ = record
  { to = λ { ⟨ aa , p ⟩ → inj₁ p ; ⟨ bb , p ⟩ → inj₂ (inj₁ p) ; ⟨ cc , p ⟩ → inj₂ (inj₂ p)
    }
    ;
    from = λ { (inj₁ b) → ⟨ aa , b ⟩ ; (inj₂ (inj₁ b)) → ⟨ bb , b ⟩ ; (inj₂ (inj₂ b)) → ⟨ cc , b ⟩ 
    }
    ;
    from∘to = λ { ⟨ aa , p ⟩ → refl ; ⟨ bb , p ⟩ → refl ; ⟨ cc , p ⟩ → refl
    }
    ;
    to∘from = λ { (inj₁ b) → refl ; (inj₂ (inj₁ b)) → refl ; (inj₂ (inj₂ b)) → refl
    }
  }








