------------------------------------------------------------------------
-- The product of two partial sums below a longer partial sum
--
-- 两个部分和之积落在更长部分和之下
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.ProductBound where

open import Data.Nat using (ℕ; zero; suc; _<_; _∸_; z≤n; s≤s)
  renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using
  (n<1+n; <-trans; m≤m+n; m+[n∸m]≡n; +-∸-assoc; <⇒≤)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Data.Rational.Properties using (≤-refl; ≤-trans; +-mono-≤; *-zeroʳ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import Real.Interval.Series.Bounds using (le-self-add)
open import Real.Interval.Kit using (*-mono-≤-nonNeg)
open import Real.Interval.Exp.Core using
  (term; sumQ; sumQ-split; sumQ-nonNeg; term-nonNeg; expPartial)
open import Real.Interval.Exp.Conv using (expPartial-mul)
open import Real.Interval.Exp.Convolve using (partial-convolve)
open import Real.Interval.Exp.Triangle using (triangle-interchange)

------------------------------------------------------------------------
-- Extending the bound of a non-negative sum
--
-- 加长非负和的上界

-- A sum of non-negative terms grows with its bound: the longer sum is the
-- shorter one plus a non-negative tail.
--
-- 非负项之和随其界单调增长：更长的和等于较短的和加上一段非负尾部。
sumQ-≤-bound : (f : ℕ → ℚ) (0≤f : ∀ k → 0ℚ ≤ f k) (m n : ℕ)
             → m ≤ℕ n → sumQ f m ≤ sumQ f n
sumQ-≤-bound f 0≤f m n m≤n =
  subst (λ z → sumQ f m ≤ z)
        (sym (trans (cong (sumQ f) (sym (m+[n∸m]≡n m≤n)))
                    (sumQ-split f m (n ∸ m))))
        (le-self-add {p = sumQ f m}
          (sumQ-nonNeg (λ i → f (m +ℕ i)) (λ i → 0≤f (m +ℕ i)) (n ∸ m)))

------------------------------------------------------------------------
-- Agreement restricted to an initial segment, for the order
--
-- 只在初始段上的序比较

-- Two sums of length `n` are ordered as soon as the summands are ordered
-- below `n`.
--
-- 只要被加项在界下有序，两条长度为 `n` 的和就有同样的序。
sumQ-mono-upto : (f g : ℕ → ℚ) (n : ℕ)
               → (∀ i → i < n → f i ≤ g i)
               → sumQ f n ≤ sumQ g n
sumQ-mono-upto f g zero h = ≤-refl
sumQ-mono-upto f g (suc n) h =
  +-mono-≤ (sumQ-mono-upto f g n (λ i i<n → h i (<-trans i<n (n<1+n n))))
           (h n (n<1+n n))

------------------------------------------------------------------------
-- The rank of a row inside the doubled cut
--
-- 倍长截角里某一行的秩

-- A row of index below `n` keeps its whole square inside the cut of rank
-- `2n`.
--
-- 指标小于 `n` 的行，在秩为 `2n` 的截角里保住了整个方形。
cut-bound : (n i : ℕ) → i ≤ℕ n → n ≤ℕ (n +ℕ n) ∸ i
cut-bound n i i≤n =
  subst (λ z → n ≤ℕ z) (sym (+-∸-assoc n {n} {i} i≤n)) (m≤m+n n (n ∸ i))

------------------------------------------------------------------------
-- Non-negativity of the pairwise products
--
-- 两两乘积的非负性

-- Each product of two terms at non-negative parameters is non-negative.
--
-- 非负参数下两个通项之积非负。
prod-nonNeg : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (i j : ℕ)
            → 0ℚ ≤ term p i * term q j
prod-nonNeg p q 0≤p 0≤q i j =
  subst (λ z → z ≤ term p i * term q j) (*-zeroʳ 0ℚ)
    (*-mono-≤-nonNeg {a = 0ℚ} {a' = term p i} {b = 0ℚ} {b' = term q j}
      (≤-refl {0ℚ}) (term-nonNeg p 0≤p i)
      (≤-refl {0ℚ}) (term-nonNeg q 0≤q j))

------------------------------------------------------------------------
-- The bound of the product
--
-- 乘积的上界

-- An equality read as an inequality, left to right.
--
-- 把等式按从左到右读成不等式。
≤-of-≡ : (x y : ℚ) → x ≡ y → x ≤ y
≤-of-≡ x y eq = subst (λ z → x ≤ z) eq (≤-refl {x})

-- Growing the inner bound of every row keeps the square inside the cut.
--
-- 每行都加长内层界，方形仍在截角之内。
inner-bound-≤ : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (n i : ℕ)
              → i < n
              → sumQ (λ j → term p i * term q j) n
                ≤ sumQ (λ j → term p i * term q j) ((n +ℕ n) ∸ i)
inner-bound-≤ p q 0≤p 0≤q n i i<n =
  sumQ-≤-bound (λ j → term p i * term q j) (prod-nonNeg p q 0≤p 0≤q i)
               n ((n +ℕ n) ∸ i) (cut-bound n i (<⇒≤ i<n))

mono-step : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (n : ℕ)
          → sumQ (λ i → sumQ (λ j → term p i * term q j) n) n
            ≤ sumQ (λ i → sumQ (λ j → term p i * term q j) ((n +ℕ n) ∸ i)) n
mono-step p q 0≤p 0≤q n =
  sumQ-mono-upto (λ i → sumQ (λ j → term p i * term q j) n)
                 (λ i → sumQ (λ j → term p i * term q j) ((n +ℕ n) ∸ i))
                 n
                 (inner-bound-≤ p q 0≤p 0≤q n)

len-step : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (n : ℕ)
         → sumQ (λ i → sumQ (λ j → term p i * term q j) ((n +ℕ n) ∸ i)) n
           ≤ sumQ (λ i → sumQ (λ j → term p i * term q j) ((n +ℕ n) ∸ i))
                  (n +ℕ n)
len-step p q 0≤p 0≤q n =
  sumQ-≤-bound (λ i → sumQ (λ j → term p i * term q j) ((n +ℕ n) ∸ i))
               (λ i → sumQ-nonNeg (λ j → term p i * term q j)
                                  (prod-nonNeg p q 0≤p 0≤q i) ((n +ℕ n) ∸ i))
               n (n +ℕ n) (m≤m+n n n)

-- The cut of rank `2n` is the partial sum at the sum of the parameters.
--
-- 秩为 `2n` 的截角就是在参数之和处的部分和。
bridge : (p q : ℚ) (n : ℕ)
       → sumQ (λ i → sumQ (λ j → term p i * term q j) ((n +ℕ n) ∸ i)) (n +ℕ n)
         ≡ expPartial (p + q) (n +ℕ n)
bridge p q n =
  sym (trans (partial-convolve p q (n +ℕ n))
             (triangle-interchange (λ i j → term p i * term q j) (n +ℕ n)))

-- The product of the two partial sums is bounded by the partial sum at
-- the sum of the parameters, taken twice as long.
--
-- 两个部分和之积，被参数之和处长度加倍的部分和所界住。
partial-mul-≤ : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (n : ℕ)
              → expPartial p n * expPartial q n
                ≤ expPartial (p + q) (n +ℕ n)
partial-mul-≤ p q 0≤p 0≤q n =
  ≤-trans (≤-of-≡ _ _ (expPartial-mul p q n))
    (≤-trans (mono-step p q 0≤p 0≤q n)
      (≤-trans (len-step p q 0≤p 0≤q n)
        (≤-of-≡ _ _ (bridge p q n))))
