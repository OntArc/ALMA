------------------------------------------------------------------------
-- The convolution identity of the exponential terms
--
-- 指数通项的卷积恒等式
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Convolve where

open import Data.Nat using (ℕ; zero; suc; _<_; _∸_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (∸-suc; n∸n≡0; m∸n+n≡m; +-comm; ≤-pred; <⇒≤)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Properties using (*-assoc; *-identityˡ; *-identityʳ; +-identityˡ)
open import Data.Rational.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import Real using (ε)
open import Real.Interval.Rational using (powQ)
open import Real.Interval.Exp.Core using (term; sumQ; sumQ-cong; expPartial)
open import Real.Interval.Exp.Factorial using (invProd; invProd-suc; coeff-step)
open import Real.Interval.Exp.Diag using (diag; diag-correct; step-split; term-suc-step)
open import Real.Interval.Exp.Conv using (*-sumQʳ)
open import Real.Interval.Exp.Splice using (head0; splice; sumQ-cong-upto)
open import Real.Interval.Exp.Lipschitz using (sumQ-add)

------------------------------------------------------------------------
-- Index arithmetic for the diagonal
--
-- 对角的指标算术

-- Cancelling one successor on each side of the truncating subtraction.
--
-- 在截断减法的两侧各消去一个后继。
∸-split : (i k : ℕ) → i < k → k ∸ i ≡ suc (k ∸ suc i)
∸-split i k i<k = ∸-suc {m = suc i} {n = k} i<k

------------------------------------------------------------------------
-- The two halves of one precision step
--
-- 一次精度步的两半

-- The half that absorbs `p` into the left exponent.
--
-- 把 `p` 并进左指数的那一半。
halfˡ : (p q : ℚ) (k i : ℕ) → ℚ
halfˡ p q k i =
  ((powQ p (suc i) * powQ q (k ∸ i)) * (invProd i * invProd (k ∸ i))) * ε k

-- The half that absorbs `q` into the right exponent.
--
-- 把 `q` 并进右指数的那一半。
halfʳ : (p q : ℚ) (k i : ℕ) → ℚ
halfʳ p q k i =
  ((powQ p i * powQ q (suc (k ∸ i))) * (invProd i * invProd (k ∸ i))) * ε k

------------------------------------------------------------------------
-- Single factors that the diagonal comparison rewrites
--
-- 对角比较中需要改写的单个因子

-- One level of the power, read through the split second index.
--
-- 一层幂，按拆分后的第二个指标读出。
powQ-∸ : (q : ℚ) (i k : ℕ) → i < k
       → powQ q (k ∸ i) ≡ q * powQ q (k ∸ suc i)
powQ-∸ q i k i<k = cong (powQ q) (∸-split i k i<k)

-- One level of the reciprocal factorial, read through the split second
-- index.
--
-- 一层阶乘倒数，按拆分后的第二个指标读出。
invProd-∸ : (i k : ℕ) → i < k
          → invProd (k ∸ i) ≡ invProd (k ∸ suc i) * ε (k ∸ suc i)
invProd-∸ i k i<k =
  trans (cong invProd (∸-split i k i<k)) (sym (invProd-suc (k ∸ suc i)))

-- The precision index is the sum of the two split indices.
--
-- 精度指标是两个拆分指标之和。
ε-∸ : (i k : ℕ) → i < k → ε k ≡ ε (i +ℕ suc (k ∸ suc i))
ε-∸ i k i<k =
  cong ε (sym (trans (cong (λ z → i +ℕ z) (sym (∸-split i k i<k)))
                     (trans (+-comm i (k ∸ i)) (m∸n+n≡m (<⇒≤ i<k)))))

------------------------------------------------------------------------
-- Pairing the two halves against one next-level summand
--
-- 把两半配对成一个下一层的被加项

-- The two halves at index `i` add up to the next-level diagonal summand at
-- index `suc i`.
--
-- 指标 `i` 处的两半之和就是指标 `suc i` 处的下一层对角被加项。
pair-diag : (p q : ℚ) (k i : ℕ) → i < k
          → halfˡ p q k i + halfʳ p q k (suc i) ≡ diag p q (suc k) (suc i)
pair-diag p q k i i<k =
  let P  = powQ p i
      Q  = powQ q (k ∸ i)
      Qm = powQ q (k ∸ suc i)
      a  = invProd i
      J  = invProd (k ∸ i)
      b  = invProd (k ∸ suc i)
      d  = ε (k ∸ suc i)
      I' = invProd (suc i)
      E  = ε k
      E' = ε (i +ℕ suc (k ∸ suc i))
  in begin
  halfˡ p q k i + halfʳ p q k (suc i)
    ≡⟨ cong (λ z → (((p * P) * z) * (a * J)) * E
                     + (((p * P) * (q * Qm)) * (I' * b)) * E)
           (powQ-∸ q i k i<k) ⟩
  (((p * P) * (q * Qm)) * (a * J)) * E
    + (((p * P) * (q * Qm)) * (I' * b)) * E
    ≡⟨ solve 9 (λ p P q Qm a J I' b E →
                  (((((p :* P) :* (q :* Qm)) :* (a :* J)) :* E)
                    :+ ((((p :* P) :* (q :* Qm)) :* (I' :* b)) :* E))
                  := (((p :* P) :* (q :* Qm))
                       :* (((a :* J) :* E) :+ ((I' :* b) :* E))))
         refl p P q Qm a J I' b E ⟩
  ((p * P) * (q * Qm)) * (((a * J) * E) + ((I' * b) * E))
    ≡⟨ cong (λ z → ((p * P) * (q * Qm)) * ((a * z) * E + (I' * b) * E))
           (invProd-∸ i k i<k) ⟩
  ((p * P) * (q * Qm)) * ((a * (b * d) * E) + (I' * b) * E)
    ≡⟨ cong (λ z → ((p * P) * (q * Qm)) * ((a * (b * d) * z) + (I' * b) * z))
           (ε-∸ i k i<k) ⟩
  ((p * P) * (q * Qm)) * ((a * (b * d) * E') + (I' * b) * E')
    ≡⟨ cong (λ z → ((p * P) * (q * Qm)) * ((a * z * E') + (I' * b) * E'))
           (invProd-suc (k ∸ suc i)) ⟩
  ((p * P) * (q * Qm)) * ((a * invProd (suc (k ∸ suc i)) * E')
                          + (I' * b) * E')
    ≡⟨ cong (λ z → ((p * P) * (q * Qm)) * z)
           (coeff-step i (k ∸ suc i)) ⟩
  ((p * P) * (q * Qm)) * (I' * invProd (suc (k ∸ suc i)))
    ≡⟨ cong (λ z → ((p * P) * (q * Qm)) * (I' * z))
           (sym (cong invProd (∸-split i k i<k))) ⟩
  ((p * P) * (q * Qm)) * (I' * J)
    ≡⟨ cong (λ z → ((p * P) * z) * (I' * J)) (sym (powQ-∸ q i k i<k)) ⟩
  ((p * P) * Q) * (I' * J) ∎

------------------------------------------------------------------------
-- The two degenerate ends of the diagonal
--
-- 对角的两端退化情形

-- At index zero only the right half survives.
--
-- 指标零处只剩右半。
zero-diag : (p q : ℚ) (k : ℕ) → halfʳ p q k 0 ≡ diag p q (suc k) 0
zero-diag p q k = begin
  halfʳ p q k 0
    ≡⟨ cong₂ (λ x y → (x * y) * ε k)
           (*-identityˡ (powQ q (suc k))) (*-identityˡ (invProd k)) ⟩
  (powQ q (suc k) * invProd k) * ε k
    ≡⟨ *-assoc (powQ q (suc k)) (invProd k) (ε k) ⟩
  powQ q (suc k) * (invProd k * ε k)
    ≡⟨ cong (powQ q (suc k) *_) (invProd-suc k) ⟩
  powQ q (suc k) * invProd (suc k)
    ≡⟨ sym (cong₂ _*_ (*-identityˡ (powQ q (suc k)))
                     (*-identityˡ (invProd (suc k)))) ⟩
  (1ℚ * powQ q (suc k)) * (1ℚ * invProd (suc k)) ∎

-- At the last index only the left half survives.
--
-- 最后一个指标处只剩左半。
end-diag : (p q : ℚ) (k : ℕ)
         → halfˡ p q k k ≡ term p (suc k) * term q (suc k ∸ suc k)
end-diag p q k = begin
  halfˡ p q k k
    ≡⟨ cong (λ z → ((powQ p (suc k) * powQ q z)
                     * (invProd k * invProd z)) * ε k)
           (n∸n≡0 k) ⟩
  ((powQ p (suc k) * 1ℚ) * (invProd k * 1ℚ)) * ε k
    ≡⟨ cong (_* ε k) (cong₂ _*_ (*-identityʳ (powQ p (suc k)))
                                (*-identityʳ (invProd k))) ⟩
  (powQ p (suc k) * invProd k) * ε k
    ≡⟨ *-assoc (powQ p (suc k)) (invProd k) (ε k) ⟩
  powQ p (suc k) * (invProd k * ε k)
    ≡⟨ cong (powQ p (suc k) *_) (invProd-suc k) ⟩
  powQ p (suc k) * invProd (suc k)
    ≡⟨ sym (cong₂ _*_ (*-identityʳ (powQ p (suc k)))
                     (*-identityʳ (invProd (suc k)))) ⟩
  (powQ p (suc k) * 1ℚ) * (invProd (suc k) * 1ℚ)
    ≡⟨ cong₂ (λ x y → (powQ p (suc k) * x) * (invProd (suc k) * y))
             (sym (cong (powQ q) (n∸n≡0 k)))
             (sym (cong invProd (n∸n≡0 k))) ⟩
  (powQ p (suc k) * powQ q (k ∸ k))
    * (invProd (suc k) * invProd (k ∸ k))
    ≡⟨ sym (diag-correct p q (suc k) (suc k)) ⟩
  term p (suc k) * term q (suc k ∸ suc k) ∎

------------------------------------------------------------------------
-- The pointwise split of the convolution summand
--
-- 卷积被加项的逐点拆分

-- A diagonal summand multiplied by the next precision is the sum of its
-- two halves.
--
-- 对角被加项乘以一层精度，就是它两半之和。
step-term : (p q : ℚ) (k i : ℕ)
          → (term p i * term q (k ∸ i)) * ((p + q) * ε k)
            ≡ halfˡ p q k i + halfʳ p q k i
step-term p q k i =
  trans (cong (_* ((p + q) * ε k)) (diag-correct p q k i)) (step-split p q k i)

-- Read one level up, the merged summand is the next-level convolution
-- term.
--
-- 升高一层后，合并后的被加项就是下一层的卷积项。
pointwise : (p q : ℚ) (k j : ℕ) → j < suc k
          → head0 (halfˡ p q k) j + halfʳ p q k j
            ≡ term p j * term q (suc k ∸ j)
pointwise p q k zero j<sk =
  trans (+-identityˡ (halfʳ p q k 0))
        (trans (zero-diag p q k) (sym (diag-correct p q (suc k) 0)))
pointwise p q k (suc i) i<sk =
  trans (pair-diag p q k i (≤-pred i<sk))
        (sym (diag-correct p q (suc k) (suc i)))

------------------------------------------------------------------------
-- The convolution identity
--
-- 卷积恒等式

-- The `k`-th term of the series at `p + q` is the diagonal sum of the
-- products of the terms at `p` and at `q`.
--
-- 在 `p + q` 处的级数第 `k` 项，等于 `p` 处与 `q` 处的通项之积的对角和。
convolve : (p q : ℚ) (k : ℕ)
         → term (p + q) k ≡ sumQ (λ i → term p i * term q (k ∸ i)) (suc k)
convolve p q zero = begin
  term (p + q) zero
    ≡⟨⟩
  1ℚ
    ≡⟨ sym (+-identityˡ 1ℚ) ⟩
  0ℚ + 1ℚ
    ≡⟨ cong (0ℚ +_) (sym (*-identityˡ 1ℚ)) ⟩
  0ℚ + 1ℚ * 1ℚ ∎
convolve p q (suc k) = begin
  term (p + q) (suc k)
    ≡⟨ term-suc-step (p + q) k ⟩
  term (p + q) k * ((p + q) * ε k)
    ≡⟨ cong (_* ((p + q) * ε k)) (convolve p q k) ⟩
  sumQ (λ i → term p i * term q (k ∸ i)) (suc k) * ((p + q) * ε k)
    ≡⟨ *-sumQʳ (λ i → term p i * term q (k ∸ i)) (suc k) ((p + q) * ε k) ⟩
  sumQ (λ i → (term p i * term q (k ∸ i)) * ((p + q) * ε k)) (suc k)
    ≡⟨ sumQ-cong _ _ (step-term p q k) (suc k) ⟩
  sumQ (λ i → halfˡ p q k i + halfʳ p q k i) (suc k)
    ≡⟨ sumQ-add (halfˡ p q k) (halfʳ p q k) (suc k) ⟩
  sumQ (halfˡ p q k) (suc k) + sumQ (halfʳ p q k) (suc k)
    ≡⟨ splice (halfˡ p q k) (halfʳ p q k) k ⟩
  sumQ (λ j → head0 (halfˡ p q k) j + halfʳ p q k j) (suc k) + halfˡ p q k k
    ≡⟨ cong (_+ halfˡ p q k k)
           (sumQ-cong-upto _ _ (suc k) (pointwise p q k)) ⟩
  sumQ (λ j → term p j * term q (suc k ∸ j)) (suc k) + halfˡ p q k k
    ≡⟨ cong (sumQ (λ j → term p j * term q (suc k ∸ j)) (suc k) +_)
           (end-diag p q k) ⟩
  sumQ (λ j → term p j * term q (suc k ∸ j)) (suc k)
    + term p (suc k) * term q (suc k ∸ suc k)
    ≡⟨⟩
  sumQ (λ j → term p j * term q (suc k ∸ j)) (suc (suc k)) ∎

------------------------------------------------------------------------
-- The partial sums at the sum of two parameters
--
-- 两参数之和处的部分和

-- Summing the convolution identity over the first `n` levels turns the
-- partial sum at `p + q` into the triangular sum of the pairwise products.
--
-- 把卷积恒等式对前 `n` 层求和，`p + q` 处的部分和就成了两两乘积的三角和。
partial-convolve : (p q : ℚ) (n : ℕ)
                 → expPartial (p + q) n
                   ≡ sumQ (λ k → sumQ (λ i → term p i * term q (k ∸ i)) (suc k)) n
partial-convolve p q n = sumQ-cong (term (p + q)) _ (convolve p q) n
