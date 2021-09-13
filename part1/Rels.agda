import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Induction` using (+-assoc; +-suc )

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

<-iff-≤ : ∀ {m n : ℕ}
  → m < n
    ---------
  → suc m ≤ n
<-iff-≤ z<s       = s≤s z≤n
<-iff-≤ (s<s m<n) = s≤s (<-iff-≤ m<n)

≤-iff-<′ : ∀ {m n : ℕ}
  → suc m ≤ n
    ---------
  → m < n
≤-iff-<′ (s≤s z≤n)       = z<s
≤-iff-<′ (s≤s (s≤s m≤n)) = s<s (≤-iff-<′ (s≤s m≤n))

-- Give an alternative proof that strict inequality is transitive,
-- using the relation between strict inequality and inequality and
-- the fact that inequality is transitive.

<-trans-revisited : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p

helper : ∀ {m n : ℕ}
  → m < n
    ---------
    → m < suc n
helper z<s       = z<s
helper (s<s m<n) = s<s (helper m<n)

<-trans-revisited z<s (s<s n<p) = ≤-iff-<′ (≤-trans (<-iff-≤ z<s) (<-iff-≤ (s<s n<p)))
<-trans-revisited (s<s m<n) (s<s n<p) = ≤-iff-<′ (≤-trans (s≤s (<-iff-≤ (helper m<n))) (<-iff-≤ (s<s n<p)))


-- Show that the sum of two odd numbers is even.

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
    ------------
  → even (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)

o+o≡e (suc zero) om = suc om
o+o≡e (suc (suc on)) om = suc (suc (o+o≡e on om ))


-- Bin-predicates 

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩    = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

to   : ℕ → Bin
from : Bin → ℕ

to 0 = ⟨⟩ O
to (suc n) = inc ( to n)

from ⟨⟩    = zero
from (b O) = 2 * (from b)
from (b I) = 2 * (from b) + 1

data One : Bin → Set where 
  one : 
     -------
     One (⟨⟩ I)
  _OO : ∀ {b : Bin} → One b → One (b O)
  _II : ∀ {b : Bin} → One b → One (b I)

data Can : Bin → Set where
  zero : Can (⟨⟩ O)
  can : ∀ {b : Bin} → One b → Can b 

-- Can b
------------
-- Can (inc b)

one_inc : ∀ {b : Bin} → One b → One (inc b)
one_inc one    = one OO
one_inc (o OO) = o II
one_inc (o II) = (one_inc o) OO

can_inc : ∀ {b : Bin} → Can b → Can (inc b)
can_inc zero = can one 
can_inc (can one) = can (one OO)
can_inc (can (o OO)) = can (o II)
can_inc (can (o II)) = can (one_inc (o II))

----------
-- Can (to n)

can_to_n : ∀ (n : ℕ) → Can (to n)
can_to_n zero = zero
can_to_n (suc n) = can_inc (can_to_n n)

-- Can b
---------------
-- to (from b) ≡ b

data even_c : Bin → Set
data odd_c  : Bin → Set

data even_c where

  zero_c :
      ---------
      even_c (⟨⟩ O)

  suc_c  : ∀ {b : Bin}
    → odd_c b
      ------------
    → even_c (inc b)

data odd_c where

  suc_c  : ∀ {b : Bin}
    → even_c b
      -----------
    → odd_c (inc b)


{-
to_bin : ∀ {b : Bin} → One (b) → Bin 
to_bin one = ⟨⟩ I
to_bin (b II) = (to_bin b) I
to_bin (b OO) = (to_bin b) O

to_from_odd : ∀ {b : Bin} → One b → Bin
to_from_odd one = to (from l)


to_from_one : ∀ {b : Bin} → One b → to (from b) ≡ b
to_from_one one = refl
to_from_one (b II) = 
  begin 
    to (from (b I))

helper_O : ∀ {b : Bin} → One (b I O) → to (from (b I O)) ≡ (to (from (b I))) O
helper_I : ∀ {b : Bin} → One (b I I) → to (from (b I I)) ≡ (to (from (b I))) I

helper_I (one II)  = refl
helper_O (one OO) = refl
helper_I ( b II II ) = 


-- to (from (b O)) = to (2 * (from b) ) = (to (from b)) O
-}


2*n≡n+n : ∀ (n : ℕ) → 2 * n ≡ n + n
2*n≡n+n n rewrite +-identityʳ n = refl

+-suc-suc : ∀ (m n : ℕ) → (suc m) + (suc n) ≡ suc (suc (m + n))
+-suc-suc m n rewrite +-suc (suc m) n | sym (+-assoc 1 m n) = refl



from∘inc≡suc∘from : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from∘inc≡suc∘from ⟨⟩ = refl
from∘inc≡suc∘from (b O) rewrite +-suc (from (b O)) zero | +-identityʳ (from (b O)) = refl
from∘inc≡suc∘from (b I) rewrite from∘inc≡suc∘from b | 2*n≡n+n (suc (from b)) | +-suc-suc (from b) (from b) | sym (2*n≡n+n (from b)) | +-comm 1 (2 * (from b)) = refl


to∘from∘inc≡inc∘to∘from : ∀ (b : Bin) → to (from (inc b)) ≡ inc (to (from b))
to∘from∘inc≡inc∘to∘from ⟨⟩ =
  begin
    to (from (inc ⟨⟩))
  ≡⟨⟩
    to (from (⟨⟩ I))
  ≡⟨⟩
    to 1
  ≡⟨⟩
    ⟨⟩ I
  ≡⟨⟩
    inc ⟨⟩
  ≡⟨⟩
    inc (to zero)
  ≡⟨⟩
    inc (to (from ⟨⟩))
  ∎
to∘from∘inc≡inc∘to∘from (b O) =
  begin
    to (from (inc (b O)))
  ≡⟨⟩
    to (from (b I))
  ≡⟨⟩
    to (2 * (from b) + 1)
  ≡⟨⟩
    to (2 * (from b) + (suc zero))
  ≡⟨ cong to (+-suc (2 * (from b)) zero) ⟩
    to (suc (2 * (from b) + zero))
  ≡⟨ cong (λ 2*fromb → to (suc 2*fromb)) (+-identityʳ (2 * (from b))) ⟩
    to (suc (2 * (from b)))
  ≡⟨⟩
    inc (to (2 * (from b)))
  ≡⟨⟩
    inc (to (from (b O)))
  ∎
to∘from∘inc≡inc∘to∘from (b I) =
  begin
    to (from (inc (b I)))
  ≡⟨⟩
    to (from ((inc b) O))
  ≡⟨⟩
    to (2 * (from (inc b)))
  ≡⟨ cong (λ suc∘fromb → to (2 * suc∘fromb)) (from∘inc≡suc∘from b) ⟩
    to (2 * (suc (from b)))
  ≡⟨ cong to (2*n≡n+n (suc (from b))) ⟩
    to ((suc (from b)) + (suc (from b)))
  ≡⟨ cong to (+-suc-suc (from b) (from b)) ⟩
    to (suc (suc ((from b) + (from b))))
  ≡⟨ cong (λ 2*fromb → to (suc (suc 2*fromb))) (sym (2*n≡n+n (from b))) ⟩
    to (suc (suc (2 * (from b))))
  ≡⟨ cong (λ 2*fromb+1 → to (suc 2*fromb+1)) (+-comm 1 (2 * (from b))) ⟩
    to (suc (2 * (from b) + 1))
  ≡⟨⟩
    to (suc (from (b I)))
  ≡⟨⟩
    inc (to (from (b I)))
  ∎

to∘from : ∀ {b : Bin} → Can b → to (from b) ≡ b
to∘from zero =
  begin
    to (from (⟨⟩ O))
  ≡⟨⟩
    to (2 * from ⟨⟩)
  ≡⟨⟩
    to (2 * zero)
  ≡⟨⟩
    to zero
  ≡⟨⟩
    ⟨⟩ O
  ∎
to∘from (can one) =
  begin
    to (from (⟨⟩ I))
  ≡⟨⟩
    to (2 * from ⟨⟩ + 1)
  ≡⟨⟩
    to (2 * zero + 1)
  ≡⟨⟩
    to 1
  ≡⟨⟩
    ⟨⟩ I
  ∎
{-
-- to∘from {b O} (can (ob OO)) = {!!} -- TODO
to∘from {b O} (can (ob OO)) =
  begin
    to (from (b O))
  ≡⟨⟩
    to (2 * from (b)))
  ≡⟨⟩
    to (from inc (b I O))
  ≡⟨ cong inc (to∘from (can (ob II OO))) ⟩
    inc (b I O)
  ≡⟨⟩
    b I
  ∎
-}
to∘from {b O} (can (ob OO)) = {!!} -- TODO
to∘from {b I} (can (ob II)) =
  begin
    to (from (b I))
  ≡⟨⟩
    to (from (inc (b O)))
  ≡⟨ to∘from∘inc≡inc∘to∘from (b O) ⟩
    inc (to (from (b O)))
  ≡⟨ cong inc (to∘from (can (ob OO))) ⟩
    inc (b O)
  ≡⟨⟩
    b I
  ∎

to_two_from : ∀ {b : Bin} → One b → to ( 2 * (from b)) ≡ (b O)
to_two_from one = refl
to_two_from {b O} (ob OO) = 
  to ( 2 * (from (b O)))
≡⟨cong to (cong (2 *_ ) (to_two_from b ob)⟩
  to ( 2 * (2 * (from b)))
≡⟨cong to (cong (2 *_) (from∘to (2 * from b))⟩
  to ( 2 * (from (to (2 * from b))))
≡⟨ cong to_two_from ( to_two_from b)) ⟩
  to_two_from
  
  



