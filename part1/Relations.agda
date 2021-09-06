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

