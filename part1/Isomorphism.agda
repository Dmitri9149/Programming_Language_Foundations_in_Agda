import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)


infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

-- Show that every isomorphism implies an embedding.

≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
    -----
  → A ≲ B

≃-implies-≲ A≃B =
  record
    { to = to A≃B
    ; from = from A≃B
    ; from∘to = from∘to A≃B
    }

{-
Define equivalence of propositions (also known as "if and only if") as follows:
```
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
```
Show that equivalence is reflexive, symmetric, and transitive.
-}

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

⇔-refl : ∀ {A : Set}
    -----
  → A ⇔ A

⇔-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    }

⇔-sym : ∀ {A B : Set}
  → A ⇔ B
    -----
  → B ⇔ A

⇔-sym A⇔B =
  record
    { to   = _⇔_.from A⇔B
    ; from = _⇔_.to A⇔B
    }

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)

⇔-trans : ∀ {A B C : Set}
  → A ⇔ B
  → B ⇔ C
    -----
  → A ⇔ C
⇔-trans A⇔B B⇔C =
  record
    { to   = _⇔_.to B⇔C   ∘ _⇔_.to A⇔B
    ; from =  _⇔_.from A⇔B ∘  _⇔_.from B⇔C
    }

{-
...define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to : ℕ → Bin
    from : Bin → ℕ

which satisfy the following property:

    from (to n) ≡ n

Using the above, establish that there is an embedding of `ℕ` into `Bin`.
-}


data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

postulate
  to`` : ℕ → Bin
  from`` : Bin → ℕ
  from∘to`` : ∀ (n : ℕ) → from`` (to`` n) ≡ n


ℕ_into_Bin : ℕ ≲ Bin
ℕ_into_Bin =
  record
    { to      = to``
    ; from    = from``
    ; from∘to = from∘to``
    }