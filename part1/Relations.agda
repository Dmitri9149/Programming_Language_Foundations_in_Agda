import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

-- Give an example of a preorder that is not a partial order.

data Rl : Set where
  A B : Rl 

data _<<_ : Rl → Rl → Set where 
  a<<a : ∀ {a : Rl} → a << a
  a<<b : ∀ {a b : Rl} → a << b

-- Give an example of a partial order that is not a total order.

data _<<<_ : Rl → Rl → Set where 
  a<<<a : ∀ {a : Rl} → a <<< a 


-- Show that multiplication is monotonic with regard to inequality.

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → (n + p) ≤ (n + q)
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → (m + p) ≤ (n + p)
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → (m + p) ≤ (n + q)
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)


*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → (m * p) ≤ (n * q)

*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → (n * p) ≤ (n * q)

*-monoʳ-≤ zero    p q p≤q  = z≤n 
*-monoʳ-≤ (suc n)    p q p≤q  = (+-mono-≤ p q (n * p) (n * q) p≤q ) (*-monoʳ-≤ n p q p≤q)

