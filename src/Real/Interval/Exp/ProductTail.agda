------------------------------------------------------------------------
-- The reverse bound for the product of two partial sums
--
-- 两个部分和之积的反向界
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.ProductTail where

open import Data.Nat using (ℕ; _<_; _∸_)
  renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using
  (∸-monoʳ-≤; m≤n⇒n∸m≤n; m+n∸n≡m; +-∸-assoc; m≤m+n; <⇒≤)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Data.Rational.Properties using (≤-refl; ≤-trans; +-mono-≤)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; trans; cong; cong₂; subst)

open import Real.Interval.Exp.Core using
  (term; sumQ; sumQ-split; term-nonNeg; expPartial)
open import Real.Interval.Exp.Conv using (expPartial-mul; *-sumQˡ; *-sumQʳ; mul-sumQ)
open import Real.Interval.Exp.Lipschitz using (sumQ-add)
open import Real.Interval.Exp.Triangle using (cut-sum)
open import Real.Interval.Exp.ProductBound using
  (sumQ-≤-bound; sumQ-mono-upto; prod-nonNeg; ≤-of-≡; bridge)

------------------------------------------------------------------------
-- The tail of a series
--
-- 级数的尾段

-- The `n` terms of the exponential series that follow index `n`.
--
-- 指数级数中紧随指标 `n` 之后的 `n` 项。
tail : (q : ℚ) (n : ℕ) → ℚ
tail q n = sumQ (λ i → term q (n +ℕ i)) n

------------------------------------------------------------------------
-- Rows below `n` split into square and spill
--
-- 指标小于 `n` 的行拆成方形与溢出

-- A row below `n` splits into its square part and the columns spilling
-- into the doubled cut.
--
-- 指标小于 `n` 的行，拆成它的方形部分与溢进倍长截角的各列。
head-split : (p q : ℚ) (n i : ℕ) → i ≤ℕ n
           → sumQ (λ j → term p i * term q j) ((n +ℕ n) ∸ i)
             ≡ sumQ (λ j → term p i * term q j) n
               + sumQ (λ j → term p i * term q (n +ℕ j)) (n ∸ i)
head-split p q n i i≤n =
  trans (cong (λ m → sumQ (λ j → term p i * term q j) m)
              (+-∸-assoc n {n} {i} i≤n))
        (sumQ-split (λ j → term p i * term q j) n (n ∸ i))

------------------------------------------------------------------------
-- The spill of a row below `n`
--
-- 指标小于 `n` 的行的溢出

-- The columns a row below `n` spills past its square stay below one
-- coefficient times the tail of the second series.
--
-- 指标小于 `n` 的行溢到方形之外的各列，不超过一个系数乘上第二条级数的尾段。
head-bound : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (n i : ℕ)
           → i < n
           → sumQ (λ j → term p i * term q j) ((n +ℕ n) ∸ i)
             ≤ sumQ (λ j → term p i * term q j) n + term p i * tail q n
head-bound p q 0≤p 0≤q n i i<n =
  let i≤n = <⇒≤ i<n
      spill : sumQ (λ j → term p i * term q (n +ℕ j)) (n ∸ i)
            ≤ term p i * tail q n
      spill =
        ≤-trans (sumQ-≤-bound (λ j → term p i * term q (n +ℕ j))
                              (λ j → prod-nonNeg p q 0≤p 0≤q i (n +ℕ j))
                              (n ∸ i) n (m≤n⇒n∸m≤n i≤n))
                (≤-of-≡ _ _ (sym (*-sumQˡ (term p i) (λ j → term q (n +ℕ j)) n)))
  in ≤-trans (≤-of-≡ _ _ (head-split p q n i i≤n))
       (+-mono-≤ (≤-refl {sumQ (λ j → term p i * term q j) n}) spill)

------------------------------------------------------------------------
-- The head half of the cut
--
-- 截角的前一半

-- The rows below `n` keep their square plus at most the product of the
-- first partial sum with the tail of the second.
--
-- 指标小于 `n` 的各行，保住方形，至多再加上第一个部分和与第二条级数尾段之积。
head-blocks : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (n : ℕ)
            → sumQ (λ i → sumQ (λ j → term p i * term q j) ((n +ℕ n) ∸ i)) n
              ≤ expPartial p n * expPartial q n + expPartial p n * tail q n
head-blocks p q 0≤p 0≤q n =
  let step : sumQ (λ i → sumQ (λ j → term p i * term q j) ((n +ℕ n) ∸ i)) n
               ≤ sumQ (λ i → sumQ (λ j → term p i * term q j) n
                                 + term p i * tail q n) n
      step = sumQ-mono-upto _ _ n (λ i i<n → head-bound p q 0≤p 0≤q n i i<n)
      split : sumQ (λ i → sumQ (λ j → term p i * term q j) n
                             + term p i * tail q n) n
              ≡ sumQ (λ i → sumQ (λ j → term p i * term q j) n) n
                + sumQ (λ i → term p i * tail q n) n
      split = sumQ-add (λ i → sumQ (λ j → term p i * term q j) n)
                       (λ i → term p i * tail q n) n
      back : sumQ (λ i → sumQ (λ j → term p i * term q j) n) n
             + sumQ (λ i → term p i * tail q n) n
             ≡ expPartial p n * expPartial q n + expPartial p n * tail q n
      back = cong₂ _+_ (sym (expPartial-mul p q n))
                       (sym (*-sumQʳ (term p) n (tail q n)))
  in ≤-trans step (≤-of-≡ _ _ (trans split back))

------------------------------------------------------------------------
-- Rows from `n` on
--
-- 从 `n` 起的各行

-- A row at index `n + i` with `i ≤ n` sees at most `n` columns in the
-- doubled cut.
--
-- 指标为 `n + i`（`i ≤ n`）的行，在读倍长截角时最多看到 `n` 列。
tail-col-bound : (n i : ℕ) → i ≤ℕ n → (n +ℕ n) ∸ (n +ℕ i) ≤ℕ n
tail-col-bound n i i≤n =
  subst (λ z → (n +ℕ n) ∸ (n +ℕ i) ≤ℕ z) (m+n∸n≡m n n)
        (∸-monoʳ-≤ (n +ℕ n) (m≤m+n n i))

-- Truncating such a row at `n` columns only enlarges it.
--
-- 把这样的行截到 `n` 列只会让它变大。
tail-row-bound : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (n i : ℕ)
               → i < n
               → sumQ (λ j → term p (n +ℕ i) * term q j) ((n +ℕ n) ∸ (n +ℕ i))
                 ≤ sumQ (λ j → term p (n +ℕ i) * term q j) n
tail-row-bound p q 0≤p 0≤q n i i<n =
  sumQ-≤-bound (λ j → term p (n +ℕ i) * term q j)
               (λ j → prod-nonNeg p q 0≤p 0≤q (n +ℕ i) j)
               ((n +ℕ n) ∸ (n +ℕ i)) n (tail-col-bound n i (<⇒≤ i<n))

-- The rows from `n` on contribute at most the tail of the first series
-- times the second partial sum.
--
-- 从 `n` 起的各行，贡献不超过第一条级数的尾段乘上第二个部分和。
tail-total : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (n : ℕ)
           → sumQ (λ i → sumQ (λ j → term p (n +ℕ i) * term q j)
                              ((n +ℕ n) ∸ (n +ℕ i))) n
             ≤ tail p n * expPartial q n
tail-total p q 0≤p 0≤q n =
  ≤-trans (sumQ-mono-upto _ _ n (λ i i<n → tail-row-bound p q 0≤p 0≤q n i i<n))
          (≤-of-≡ _ _ (sym (mul-sumQ (λ i → term p (n +ℕ i)) (term q) n n)))

------------------------------------------------------------------------
-- The two halves of the cut
--
-- 截角的两半

-- Splitting the cut at `n` separates the rows below `n` from the rows
-- from `n` on.
--
-- 在 `n` 处拆开截角，就把指标小于 `n` 的各行与从 `n` 起的各行分开。
outer-split : (f : ℕ → ℚ) (n : ℕ)
            → sumQ f (n +ℕ n) ≡ sumQ f n + sumQ (λ i → f (n +ℕ i)) n
outer-split f n = sumQ-split f n n

------------------------------------------------------------------------
-- The reverse inequality
--
-- 反向不等式

-- The doubled cut at the sum of the parameters is bounded by the product
-- of the two partial sums plus the two tail corrections.
--
-- 参数之和处的倍长截角，被两个部分和之积加上两个尾段修正所界住。
cut-≤ : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (n : ℕ)
      → cut-sum (λ i j → term p i * term q j) (n +ℕ n)
        ≤ expPartial p n * expPartial q n + expPartial p n * tail q n
          + tail p n * expPartial q n
cut-≤ p q 0≤p 0≤q n =
  let f' = λ i → sumQ (λ j → term p i * term q j) ((n +ℕ n) ∸ i)
      sp = outer-split f' n
  in ≤-trans (≤-of-≡ _ _ sp)
       (+-mono-≤ (head-blocks p q 0≤p 0≤q n) (tail-total p q 0≤p 0≤q n))

-- The partial sum at the sum of the parameters, taken twice as long, is
-- bounded by the product of the two partial sums plus the two tails.
--
-- 参数之和处长度加倍的部分和，被两个部分和之积加上两个尾段所界住。
partial-mul-upper :
  (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (n : ℕ)
  → expPartial (p + q) (n +ℕ n)
    ≤ expPartial p n * expPartial q n + expPartial p n * tail q n
      + tail p n * expPartial q n
partial-mul-upper p q 0≤p 0≤q n =
  ≤-trans (≤-of-≡ _ _ (sym (bridge p q n))) (cut-≤ p q 0≤p 0≤q n)
