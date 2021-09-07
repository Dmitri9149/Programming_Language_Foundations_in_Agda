import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

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

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → (m * p) ≤ (n * p)
*-monoˡ-≤ m n p m≤n  rewrite *-comm m p | *-comm n p  = *-monoʳ-≤ p m n m≤n

*-mono-≤ m n p q m≤n p≤q  =  ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

-- Show that strict inequality is transitive.

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans z<s       (s<s _)          =  z<s
<-trans (s<s m<n) (s<s n<p)  =  s<s (<-trans m<n n<p)

-- Show that strict inequality satisfies a weak version of trichotomy, in
-- the sense that for any `m` and `n` that one of the following holds:
--  * `m < n`,
--  * `m ≡ n`, or
--  * `m > n`.

-- Define `m > n` to be the same as `n < m`.
-- You will need a suitable data declaration,
-- similar to that used for totality.

data Trichotomy (m n : ℕ) : Set where

  up :
      m < n
      ---------
    → Trichotomy m n

  down :
      n < m
      ---------
    → Trichotomy m n

  equal :
      m ≡ n
      ---------
    → Trichotomy m n

trichotomy : ∀ (m n : ℕ) → Trichotomy m n

trichotomy zero    zero                         =  equal refl
trichotomy zero    (suc n)                         =  up z<s
trichotomy (suc m) zero                      =  down z<s
trichotomy (suc m) (suc n) with trichotomy m n
...                        | up m<n  =  up (s<s m<n)
...                        | down n<m  =  down (s<s n<m)
...                        | equal refl = equal refl
      
-- Show that addition is monotonic with respect to strict inequality.
-- As with inequality, some additional definitions may be required.

-- ∀ {m n p q : ℕ} → m < n → p < q → m + p < n + q

+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q
    -------------
  → n + p < n + q
+-monoʳ-< zero    p q p<q  =  p<q
+-monoʳ-< (suc n) p q p<q  =  s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    -------------
  → m + p < n + p
+-monoˡ-< m n p m<n  rewrite +-comm m p | +-comm n p  = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    -------------
  → m + p < n + q
+-mono-< m n p q m<n p<q  =  <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

-- Show that `suc m ≤ n` implies `m < n`, and conversely.

≤-iff-< : ∀ (m n : ℕ)

  → suc m ≤ n
    ---------
  → m < n

≤-iff-< zero _ (s≤s _) = z<s
≤-iff-< (suc _) (suc _) (s≤s m≤n) = s<s (≤-iff-< _ _ m≤n)

≤-iff-<′ : ∀ {m n : ℕ}
  → suc m ≤ n
    ---------
  → m < n
≤-iff-<′ (s≤s z≤n)       = z<s
≤-iff-<′ (s≤s (s≤s m≤n)) = s<s (≤-iff-<′ (s≤s m≤n))


