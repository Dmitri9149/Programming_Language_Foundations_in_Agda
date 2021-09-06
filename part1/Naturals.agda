import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm;
  ≤-refl; ≤-trans; ≤-antisym; ≤-total; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
-- open import plfa.part1.Relations using (_<_; z<s; s<s; zero; suc; even; odd)

{-Write out `7` in longhand. -}
seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{- some proofs-}
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

-- Compute `3 + 4`, writing out your reasoning as a chain of 
-- equations, using the equations for `+`.

_ : 3 + 4 ≡ 7
_ = 
  begin
    3 + 4 
  ≡⟨⟩
    suc (suc (suc zero)) + (suc (suc (suc (suc zero))))
  ≡⟨⟩
    suc ((suc (suc zero) + suc (suc (suc (suc zero)))))
  ≡⟨⟩
    suc ((suc ((suc (zero) + suc (suc (suc (suc zero)))))))
  ≡⟨⟩
    suc (suc (suc (suc (suc (suc (suc zero))))))
  ≡⟨⟩
    7
  ∎

  {- some proof example-}

_ : 2 * 3 ≡ 6
_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎
  
-- Compute `3 * 4`, writing out your reasoning as a chain of 
-- equations, using the equations for `*`.
-- (You do not need to step through the evaluation of `+`.)  

_ : 3 * 4 ≡  12
_ = 
  begin 
    3 * 4 
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    12
  ∎
    
{- use reflection-}

_ : 2 + 3 ≡ 5
_ = refl

{- exponentiation -}

_^_ : ℕ → ℕ → ℕ
m ^ zero = suc zero 
m ^ (suc n) = m * (m ^ n)

-- Check that `3 ^ 4` is `81`.

_ : 3 ^ 4 ≡ 81
_ = 
  begin 
    3 ^ 4 
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩ 81
  ∎

  -- Compute 5 ∸ 3 and 3 ∸ 5, writing 
  -- out your reasoning as a chain of equations.

_ = 
  begin 
    5 ∸ 3 
  ≡⟨⟩ 
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

_+++_ : ℕ → ℕ → ℕ
zero +++ zero = zero
zero +++ suc n = n
suc m +++ n = suc (m + n)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

{-
Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have:

    inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.
-}

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (⟨⟩ I) = ⟨⟩ I O
inc (⟨⟩ O) = ⟨⟩ I
inc (⟨⟩ I O) = ⟨⟩ I I 
inc (⟨⟩ I I) = ⟨⟩ I O O
inc (n O) = n I
inc (n I) = ((inc n) O)

{- check correctness for some representations -}

_ : inc (⟨⟩ O) ≡ ⟨⟩ I

_ = begin
      inc (⟨⟩ O)
  ≡⟨⟩
      ⟨⟩ I
  ∎

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O

_ = begin 
      inc (⟨⟩ I)        
  ≡⟨⟩
      ((inc ⟨⟩) O) 
  ≡⟨⟩  
      ⟨⟩ I O
  ∎

_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I 
_ = begin 
      inc (⟨⟩ I O)
  ≡⟨⟩
      ⟨⟩ I I
  ∎

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = begin 
      ((inc (⟨⟩ I)) O)
    ≡⟨⟩
      ((⟨⟩ I O) O)    
    ∎

_ : inc (⟨⟩ I I O) ≡ ⟨⟩ I I I 
_ = begin 
      inc (⟨⟩ I I O)
  ≡⟨⟩
      ⟨⟩ I I I 
  ∎

{- ... define a pair of functions to convert between the two representations -}

to   : ℕ → Bin
from : Bin → ℕ

-- For the former, choose the bitstring to have no leading zeros if it 
-- represents a positive natural, and represent zero by ⟨⟩ O. 
-- Confirm that these both give the correct answer for zero 
-- through four.

to 0 = ⟨⟩ O
to 1 = ⟨⟩ I 
to (suc n) = inc ( to n)

from (⟨⟩ O) = 0
from ⟨⟩ = 0
from (⟨⟩ I) = 1
from (b O) = 2 * from b
from (b I) = 2 * from b + 1







     




