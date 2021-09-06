module Induction` where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
{-
-- Write out what is known about associativity of addition on each of the
-- first four days using a finite story of creation.

-- On the first day, we know zero.
0 : ℕ

-- Second day : 
0 : ℕ
1 : ℕ
0 + (0 + 0) = (0 + 0) + 0 

-- Third day 
0 : ℕ
1 : ℕ 
0 + (0 + 0) = (0 + 0) + 0

2 : ℕ 
(0 + 1) + 0 = 0 + (1 + 0)
(1 + 0) + 0 = 1 + (0 + 0)
(0 + 0) + 1 = 0 + (0 + 1)

-- Fouth day 
0 : ℕ
1 : ℕ
2 : ℕ
3 : ℕ
(0 + 1) + 1 = 0 + (1 + 1)
(1 + 1) + 0 = 1 + (1 + 0)
(1 + 0) + 1 = 1 + (0 + 1)

-}

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero    n p                          =  refl
+-assoc (suc m) n p  
  rewrite +-assoc m n p  =  refl

+-identity : ∀ (n : ℕ) → n + zero ≡ n
+-identity zero = refl
+-identity (suc n) 
  rewrite +-identity n = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n 
  rewrite +-suc m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero 
  rewrite +-identity m = refl
+-comm m (suc n) 
  rewrite +-suc m n | +-comm m n = refl

-- Show

--    m + (n + p) ≡ n + (m + p)

-- for all naturals `m`, `n`, and `p`. No induction is needed,
-- just apply the previous results which show addition
-- is associative and commutative.

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p 
  rewrite sym (+-assoc m n p)
        | sym (+-assoc n m p)
        | +-comm m n
        = refl

-- Show multiplication distributes over addition, that is,

--    (m + n) * p ≡ m * p + n * p

-- for all naturals `m`, `n`, and `p`.

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p
  rewrite cong (p +_) (*-distrib-+ m n p)
        | +-assoc p (m * p) (n * p)
        = refl

-- Show multiplication is associative, that is,

--    (m * n) * p ≡ m * (n * p)

-- for all naturals `m`, `n`, and `p`.

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)

*-assoc zero n p = refl
*-assoc (suc m) n p 
  rewrite *-distrib-+ n (m * n) p
    | cong ((n * p) +_) (*-assoc m n p) 
    = refl
    

-- Show multiplication is commutative, that is,
--     m * n ≡ n * m
-- for all naturals `m` and `n`.  As with commutativity of addition,
-- you will need to formulate and prove suitable lemmas.

*-zero : ∀ (n : ℕ) → n * zero ≡ zero
*-zero zero = refl
*-zero (suc n) rewrite *-zero n = refl


*-suc : ∀ (m n : ℕ) → m * (suc n) ≡ m * n + m 
*-suc zero zero = refl
*-suc zero n = 
  begin 
    zero * (suc n)
  ≡⟨⟩
    zero * n + zero
  ∎
   
*-suc (suc m) n = 
  begin  
    (suc m) * (suc n)
  ≡⟨⟩
    (suc n) + (m * (suc n))
  ≡⟨ cong ((suc n) +_) (*-suc m n) ⟩
    (suc n) + ((m * n) + m)
  ≡⟨⟩
    suc (n + ((m * n) + m))
  ≡⟨ cong suc (sym (+-assoc n (m * n) m)) ⟩
    suc ((n + (m * n)) + m)
  ≡⟨ sym (+-suc (n + (m * n)) m) ⟩
    (n + (m * n)) + (suc m) 
  ≡⟨⟩
    ((suc m) * n) + (suc m)
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero zero = refl
*-comm (suc m) zero =
  begin
    (suc m) * zero
  ≡⟨⟩
    zero + (m * zero)
  ≡⟨ *-comm m zero ⟩
    (zero * m)
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero * (suc m)
  ∎
*-comm zero (suc n) =
  begin
    zero * (suc n)
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero + (zero * n)
  ≡⟨ *-comm zero n ⟩
    zero + (n * zero)
  ≡⟨⟩
    (suc n) * zero
  ∎
*-comm (suc m) (suc n) =
  begin
    (suc m) * (suc n)
  ≡⟨⟩
    (suc n) + (m * (suc n))
  ≡⟨ cong ((suc n) +_) (*-comm m (suc n)) ⟩
    (suc n) + ((suc n) * m)
  ≡⟨⟩
    (suc n) + (m + (n * m))
  ≡⟨ +-swap (suc n) m (n * m) ⟩
    m + ((suc n) + (n * m))
  ≡⟨ sym (+-assoc m (suc n) (n * m)) ⟩
    (m + (suc n)) + (n * m)
  ≡⟨ cong (_+ (n * m)) (+-suc m n) ⟩
    suc (m + n) + (n * m)
  ≡⟨ cong suc (+-assoc m n (n * m)) ⟩
    (suc m) + (n + (n * m))
  ≡⟨ cong ((suc m) +_) (cong (n +_) (*-comm n m)) ⟩
    (suc m) + (n + (m * n))
  ≡⟨⟩
    (suc m) + ((suc m) * n)
  ≡⟨ cong ((suc m) +_) (*-comm ((suc m)) n) ⟩
    (suc m) + (n * (suc m))
  ≡⟨⟩
    (suc n) * (suc m)
  ∎

{-
Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?
-}
0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

{-
Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.
-}

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m n zero
  rewrite +-identity n = refl
∸-+-assoc zero n p 
  rewrite cong (_∸ p) (0∸n≡0 n)
  | 0∸n≡0 p
  | 0∸n≡0 (n + p) 
  = refl
∸-+-assoc m zero p = refl
∸-+-assoc (suc m) (suc n) p 
  rewrite (∸-+-assoc m n p)
  = refl

 {-
 Show the following three laws

     m ^ (n + p) ≡ (m ^ n) * (m ^ p)  (^-distribˡ-|-*)
     (m * n) ^ p ≡ (m ^ p) * (n ^ p)  (^-distribʳ-*)
     (m ^ n) ^ p ≡ m ^ (n * p)        (^-*-assoc)

for all `m`, `n`, and `p`.
 -}

*-identityˡ : ∀ (n : ℕ) → 1 * n ≡ n
*-identityˡ zero    = refl
*-identityˡ (suc n) 
  rewrite (+-identity n) 
  = refl

*-swap : ∀ (m n p : ℕ) → m * n * p ≡ m * p * n
*-swap m n p 
  rewrite 
    *-assoc m n p
    | cong (m *_) (*-comm n p)
    | sym (*-assoc m p n)
    = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p)
  rewrite
    cong ((m * n) *_) (^-distribʳ-* m n p)
    | sym (*-assoc (m * n) (m ^ p) (n ^ p))
    | cong (_* (n ^ p)) (*-swap m n (m ^ p))
    | *-assoc (m * (m ^ p)) n (n ^ p)
    = refl

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p 
  rewrite
    sym (*-identityˡ (m ^ p))
    | +-comm (m ^ p) 0
    | +-comm (m ^ p) 0 = refl
^-distribˡ-+-* zero (suc n) p = refl
^-distribˡ-+-* (suc m) (suc n) p
  rewrite
    cong ((suc m) *_) (^-distribˡ-+-* ((suc m)) n p)
    | sym (*-assoc (suc m) (suc m ^ n) (suc m ^ p))
    = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero 
  rewrite 
    cong (m ^_) (*-comm n zero)
    = refl
^-*-assoc m n (suc p)
  rewrite
    cong ((m ^ n) *_) (^-*-assoc m n p)
    | sym (^-distribˡ-+-* m n (n * p))
    | cong (m ^_) (cong (n +_) (*-comm n p)) 
    | cong (m ^_) (*-comm (suc p) n)
    = refl

{-
Recall that
Exercise [Bin](/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `b`
over bitstrings:

    from (inc b) ≡ suc (from b)
    to (from b) ≡ b
    from (to n) ≡ n

For each law: if it holds, prove; if not, give a counterexample.
-}

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) 
  rewrite 
    cong suc (+-identityʳ m)
    = refl

2*n≡n+n : ∀ (n : ℕ) → 2 * n ≡ n + n
2*n≡n+n n
  rewrite
    cong (n +_) (+-identityʳ n)
  = refl
    
+-suc_suc : ∀ (m n : ℕ) → (suc m) + (suc n) ≡ suc (suc (m + n))
+-suc_suc m n 
  rewrite
    +-suc (suc m) n
    | cong suc (sym (+-assoc 1 m n))
    = refl 

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩    = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

to : ℕ → Bin
to zero    = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩    = zero
from (b O) = 2 * (from b)
from (b I) = 2 * (from b) + 1

from∘inc≡suc∘from : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from∘inc≡suc∘from ⟨⟩ = refl
from∘inc≡suc∘from (b O) 
  rewrite
    +-suc (from (b O)) zero
    | cong suc (+-identityʳ (from (b O)))
    = refl
from∘inc≡suc∘from (b I) 
  rewrite 
    cong (2 *_) (from∘inc≡suc∘from b)
    | 2*n≡n+n (suc (from b))
    | +-suc_suc (from b) (from b)
    | cong suc (cong suc (sym(2*n≡n+n (from b))))
    | cong suc (+-comm 1 (2 * (from b)))
    = refl  
  
from∘to : ∀ (n : ℕ) → from (to n) ≡ n
from∘to zero = refl
from∘to (suc n)
  rewrite
    from∘inc≡suc∘from (to n)
    | cong suc (from∘to n)
    = refl







