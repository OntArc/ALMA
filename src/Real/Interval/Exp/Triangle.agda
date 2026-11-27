------------------------------------------------------------------------
-- The two readings of the triangular sum
--
-- 三角和的两种读法
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Triangle where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _∸_)
open import Data.Nat.Properties using (∸-suc; n∸n≡0; ≤-pred)
open import Data.Rational using (ℚ; 0ℚ; _+_)
open import Data.Rational.Properties using (+-identityʳ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import Real.Interval.Exp.Core using (sumQ)
open import Real.Interval.Exp.Splice using (sumQ-cong-upto)
open import Real.Interval.Exp.Lipschitz using (sumQ-add)

------------------------------------------------------------------------
-- Each level against the cut corner
--
-- 逐层与截角

-- The sum accumulated level by level: level `k` carries the summands with
-- index `i` on the diagonal `i + j = k`.
--
-- 逐层累加的和：第 `k` 层带的是对角线 `i + j = k` 上指标 `i` 的被加项。
level-sum : (f : ℕ → ℕ → ℚ) (n : ℕ) → ℚ
level-sum f n = sumQ (λ k → sumQ (λ i → f i (k ∸ i)) (suc k)) n

-- The same triangle cut by rank: index `i` sees every column `j` below
-- the remaining rank.
--
-- 同一个三角按秩截开：指标 `i` 看到剩余秩以内的全部列。
cut-sum : (f : ℕ → ℕ → ℚ) (n : ℕ) → ℚ
cut-sum f n = sumQ (λ i → sumQ (λ j → f i j) (n ∸ i)) n

------------------------------------------------------------------------
-- The row split and the vanishing last row
--
-- 行拆分与消失的末行

-- One more rank on a row splits that row into its old columns and the
-- last diagonal cell.
--
-- 某一行多出一格秩，就把该行拆成原有的各列与最后一个对角格。
inner-split : (f : ℕ → ℕ → ℚ) (n i : ℕ) → i ≤ n
            → sumQ (λ j → f i j) (suc n ∸ i)
              ≡ sumQ (λ j → f i j) (n ∸ i) + f i (n ∸ i)
inner-split f n i i≤n =
  cong (λ m → sumQ (λ j → f i j) m) (∸-suc {m = i} {n = n} i≤n)

-- The last row of the cut is empty.
--
-- 截角的最后一行是空的。
cut-zero : (f : ℕ → ℕ → ℚ) (n : ℕ)
         → sumQ (λ j → f n j) (n ∸ n) ≡ 0ℚ
cut-zero f n = cong (λ m → sumQ (λ j → f n j) m) (n∸n≡0 n)

-- Removing the last row of the cut changes nothing.
--
-- 去掉截角的最后一行，一切不变。
cut-drop : (f : ℕ → ℕ → ℚ) (n : ℕ)
         → sumQ (λ i → sumQ (λ j → f i j) (n ∸ i)) (suc n)
           ≡ sumQ (λ i → sumQ (λ j → f i j) (n ∸ i)) n
cut-drop f n =
  trans (cong (sumQ (λ i → sumQ (λ j → f i j) (n ∸ i)) n +_)
               (cut-zero f n))
        (+-identityʳ (sumQ (λ i → sumQ (λ j → f i j) (n ∸ i)) n))

------------------------------------------------------------------------
-- One more rank on the cut
--
-- 截角多出一格秩

-- Extending the cut by one rank adds exactly the new level.
--
-- 把截角延长一格秩，恰好多出新的那一层。
cut-step : (f : ℕ → ℕ → ℚ) (n : ℕ)
         → cut-sum f (suc n)
           ≡ cut-sum f n + sumQ (λ i → f i (n ∸ i)) (suc n)
cut-step f n = begin
  cut-sum f (suc n)
    ≡⟨ sumQ-cong-upto (λ i → sumQ (λ j → f i j) (suc n ∸ i))
                     (λ i → sumQ (λ j → f i j) (n ∸ i) + f i (n ∸ i))
                     (suc n)
                     (λ i i<sn → inner-split f n i (≤-pred i<sn)) ⟩
  sumQ (λ i → sumQ (λ j → f i j) (n ∸ i) + f i (n ∸ i)) (suc n)
    ≡⟨ sumQ-add (λ i → sumQ (λ j → f i j) (n ∸ i))
               (λ i → f i (n ∸ i)) (suc n) ⟩
  sumQ (λ i → sumQ (λ j → f i j) (n ∸ i)) (suc n)
    + sumQ (λ i → f i (n ∸ i)) (suc n)
    ≡⟨ cong (_+ sumQ (λ i → f i (n ∸ i)) (suc n)) (cut-drop f n) ⟩
  sumQ (λ i → sumQ (λ j → f i j) (n ∸ i)) n
    + sumQ (λ i → f i (n ∸ i)) (suc n) ∎

------------------------------------------------------------------------
-- The interchange of the two readings
--
-- 两种读法的换序

-- Summing the diagonal levels one by one is the same as summing the cut
-- rows one by one.
--
-- 按对角线逐层求和，与按截开的各行求和，结果相同。
triangle-interchange : (f : ℕ → ℕ → ℚ) (n : ℕ) → level-sum f n ≡ cut-sum f n
triangle-interchange f zero = refl
triangle-interchange f (suc n) = begin
  level-sum f (suc n)
    ≡⟨⟩
  level-sum f n + sumQ (λ i → f i (n ∸ i)) (suc n)
    ≡⟨ cong (_+ sumQ (λ i → f i (n ∸ i)) (suc n))
           (triangle-interchange f n) ⟩
  cut-sum f n + sumQ (λ i → f i (n ∸ i)) (suc n)
    ≡⟨ sym (cut-step f n) ⟩
  cut-sum f (suc n) ∎
