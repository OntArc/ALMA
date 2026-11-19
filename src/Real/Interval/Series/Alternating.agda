------------------------------------------------------------------------
-- Series: alternating partial sums
--
-- 级数：交错部分和
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Series.Alternating where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Rational using (0ℚ; _+_) renaming (-_ to neg)
open import Data.Rational.Properties using (+-assoc; +-identityˡ; +-inverseˡ)
open import Relation.Binary.PropositionalEquality using
  (sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import Real.IntervalEquiv using (centre)
open import Real.Interval using (RealI)
open import Real.Interval.Arith using (0ℝ; negℝ; _+ℝ_; _-ℝ_)
open import Real.Interval.ArithLaws using
  (+ℝ-assoc; +ℝ-identityʳ; +ℝ-inverseʳ; negℝ-0ℝ; x-ℝx)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Infimum using (≤ℝ-neg)
open import Real.Interval.Kit using (≈ℝ-of-eq)
open import Real.Interval.Mul.Order using (+ℝ-cong)
open import Real.Interval.Node using (centre-add; centre-sub)
open import Real.Interval.OrderLe using (≤ℝ-refl; ≤ℝ-resp-≈; ≤ℝ-+-mono; ≤ℝ-+-monoˡ)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.Series.Core using (sum; sum-nonNeg; x≤x+y)

------------------------------------------------------------------------
-- Negation of a non-negative number is non-positive
--
-- 非负数取负后非正

-- An alternating series is a sequence of terms whose signs flip and whose
-- sizes shrink. The repository has no parity machinery in the real layer
-- (and the `_<?_` with-abstraction is unavailable under --double-check),
-- so the parity is folded into the recursion: one step of `alt` adds two
-- terms, "minus the odd one plus the even one", which is exactly the
-- two-step pattern that the remainder estimate needs.
-- The pairing makes the analysis local: a pair
--     pair a n = a n - a (suc n)
-- is non-negative once the sizes shrink, and it is bounded by the first
-- term of the pair once the terms are non-negative. Both facts are proved
-- here from the repository's existing order and inverse laws; the
-- telescoping that turns these pairs into a single remainder bound is the
-- next step.
--     pair a n = a n - a (suc n)
-- Read off from ≤ℝ-neg (negation reverses the order) at 0 ≤ x, with
-- negℝ 0ℝ ≈ 0ℝ on the right endpoint.
--
-- 交错级数就是符号翻转、尺寸收缩的项序列。本仓实数层没有奇偶机器
-- （`--double-check` 下带 `_<?_` 的 with 也不可用），于是把奇偶折进递归里：
-- `alt` 的一步加两项，"减奇数项加偶数项"，正好是余项估计需要的两步形态。
-- 配对使分析局部化：一旦尺寸收缩，配对
-- 就非负；一旦各项非负，它就被该配对的首项所界。两条都在此由仓里现有的
-- 序律与逆元律证出；把这些配对伸缩成单一余项界的那一步是下一步。
-- 由 ≤ℝ-neg（取负反序）在 0 ≤ x 处读出，右端点用 negℝ 0ℝ ≈ 0ℝ。
negNonNeg : {x : RealI} → 0ℝ ≤ℝ x → negℝ x ≤ℝ 0ℝ
negNonNeg {x} 0≤x =
  ≤ℝ-resp-≈ ≈ℝ-refl negℝ-0ℝ (≤ℝ-neg {x = 0ℝ} {y = x} 0≤x)

------------------------------------------------------------------------
-- Pair and alternating partial sum
--
-- 配对与交错部分和

-- alt a (suc (suc n)) = alt a n + pair a n, so even and odd lengths are
-- both handled by one recursion and no parity test is ever needed.
--
-- alt a (suc (suc n)) = alt a n + pair a n，所以偶长与奇长都由同一递归
-- 处理，永不出现奇偶测试。
pair : (ℕ → RealI) → ℕ → RealI
pair a n = a n -ℝ a (suc n)

alt : (ℕ → RealI) → ℕ → RealI
alt a zero           = 0ℝ
alt a (suc zero)     = a zero
alt a (suc (suc n))  = alt a n +ℝ pair a n

------------------------------------------------------------------------
-- Pairs of a shrinking sequence are non-negative
--
-- 收缩序列的配对非负

-- a (suc n) ≤ a n, add negℝ (a (suc n)) on the right, and the left
-- endpoint collapses to 0 by the right inverse law.
--
-- 由 a (suc n) ≤ a n，右加 negℝ (a (suc n))，左端点按右逆元律坍缩成 0。
pair-nonNeg : (a : ℕ → RealI) (dec : ∀ n → a (suc n) ≤ℝ a n) (n : ℕ)
            → 0ℝ ≤ℝ pair a n
pair-nonNeg a dec n =
  ≤ℝ-resp-≈ (+ℝ-inverseʳ (a (suc n))) ≈ℝ-refl
    (≤ℝ-+-mono {x = a (suc n)} {y = a n} {z = negℝ (a (suc n))} (dec n))

------------------------------------------------------------------------
-- A pair is bounded by its first term
--
-- 配对被其首项所界

-- When all terms are non-negative, negℝ (a (suc n)) ≤ 0, so adding a n on
-- the left keeps the pair below a n + 0 ≈ a n. This is the inequality that
-- makes the sum of pairs stay below the first omitted term.
--
-- 各项非负时 negℝ (a (suc n)) ≤ 0，故左加 a n 后配对不超过 a n + 0 ≈ a n。
-- 正是这条不等式让配对之和不超过首个被略去的项。
pair-le : (a : ℕ → RealI) (0≤a : ∀ n → 0ℝ ≤ℝ a n) (n : ℕ)
        → pair a n ≤ℝ a n
pair-le a 0≤a n =
  ≤ℝ-resp-≈ ≈ℝ-refl (+ℝ-identityʳ (a n))
    (≤ℝ-+-monoˡ {x = negℝ (a (suc n))} {y = 0ℝ} {z = a n}
      (negNonNeg (0≤a (suc n))))

------------------------------------------------------------------------
-- Two-step monotonicity of the alternating sums
--
-- 交错和的两步单调性

-- alt a n ≤ alt a (n + 2), directly from the non-negativity of the pair.
--
-- alt a n ≤ alt a (n + 2)，直接由配对的非负性得出。
alt-step-mono : (a : ℕ → RealI) (dec : ∀ n → a (suc n) ≤ℝ a n) (n : ℕ)
              → alt a n ≤ℝ alt a (suc (suc n))
alt-step-mono a dec n =
  x≤x+y (alt a n) (pair a n) (pair-nonNeg a dec n)

------------------------------------------------------------------------
-- Differences telescope
--
-- 差可伸缩

-- (x - y) + (y - z) ≈ x - z: the inner y cancels. Proved level by level;
-- the ℚ step is associativity, the left inverse, and the left unit.
--
-- (x - y) + (y - z) ≈ x - z：中间的 y 消掉。逐层证，ℚ 那一步是结合律、
-- 左逆元与左单位。
sub-add-sub : (x y z : RealI) → (x -ℝ y) +ℝ (y -ℝ z) ≈ℝ x -ℝ z
sub-add-sub x y z = ≈ℝ-of-eq _ _ λ n →
  let
    cx = centre x n
    cy = centre y n
    cz = centre z n
  in
  begin
      centre ((x -ℝ y) +ℝ (y -ℝ z)) n
    ≡⟨ centre-add (x -ℝ y) (y -ℝ z) n ⟩
      centre (x -ℝ y) n + centre (y -ℝ z) n
    ≡⟨ cong₂ _+_ (centre-sub x y n) (centre-sub y z n) ⟩
      (cx + neg cy) + (cy + neg cz)
    ≡⟨ +-assoc cx (neg cy) (cy + neg cz) ⟩
      cx + (neg cy + (cy + neg cz))
    ≡⟨ cong (cx +_) (sym (+-assoc (neg cy) cy (neg cz))) ⟩
      cx + ((neg cy + cy) + neg cz)
    ≡⟨ cong (λ w → cx + (w + neg cz)) (+-inverseˡ cy) ⟩
      cx + (0ℚ + neg cz)
    ≡⟨ cong (cx +_) (+-identityˡ (neg cz)) ⟩
      cx + neg cz
    ≡⟨ sym (centre-sub x z n) ⟩
      centre (x -ℝ z) n
    ∎

------------------------------------------------------------------------
-- Telescoping
--
-- 伸缩

-- The sum of consecutive differences collapses to the outer difference:
--     Σ_{j<m} (b j - b (j+1)) ≈ b 0 - b m
-- This is the engine of the remainder estimate: the alternating tail is a
-- sum of pairs, each pair dominated by a consecutive difference, so the
-- tail is dominated by one difference of the term sequence.
--     Σ_{j<m} (b j - b (j+1)) ≈ b 0 - b m
--
-- 逐段差之和坍缩为两端之差：
-- 这就是余项估计的引擎：交错尾部是一堆配对之和，每个配对被一段相邻差
-- 所支配，于是尾部被项序列的一段差所支配。
telescope-sum : (b : ℕ → RealI) (m : ℕ)
          → sum (λ j → b j -ℝ b (suc j)) m ≈ℝ b zero -ℝ b m
telescope-sum b zero    = ≈ℝ-sym (x-ℝx (b zero))
telescope-sum b (suc m) =
  ≈ℝ-trans
    (+ℝ-cong (telescope-sum b m) ≈ℝ-refl)
    (sub-add-sub (b zero) (b m) (b (suc m)))
------------------------------------------------------------------------
-- Adding up an inequality term by term
--
-- 逐项累加不等式

-- If every term of f is below the corresponding term of g, then the same
-- holds for the partial sums: induction plus the two addition monotonicity
-- laws (the sum so far on the right, the current term on the left).
--
-- 若 f 的每一项都不超过 g 的对应项，则部分和同样如此：归纳，配两条加法
-- 单调律（右边加已求和的部分，左边加当前项）。
sum-mono : (f g : ℕ → RealI) (le : ∀ n → f n ≤ℝ g n) (m : ℕ)
         → sum f m ≤ℝ sum g m
sum-mono f g le zero    = ≤ℝ-refl
sum-mono f g le (suc m) =
  ≤ℝ-trans
    (≤ℝ-+-mono {x = sum f m} {y = sum g m} {z = f m} (sum-mono f g le m))
    (≤ℝ-+-monoˡ {x = f m} {y = g m} {z = sum g m} (le m))

------------------------------------------------------------------------
-- Subtraction is antitone in its subtrahend
--
-- 减法对减数反单调

-- y ≤ z gives x - z ≤ x - y: negate (order reverses), then add x on the
-- left, which is exactly the left-addition monotonicity.
--
-- y ≤ z 给出 x - z ≤ x - y：先取负（序反），再左加 x，正是左加单调律。
sub-anti : (x y z : RealI) → y ≤ℝ z → x -ℝ z ≤ℝ x -ℝ y
sub-anti x y z y≤z =
  ≤ℝ-+-monoˡ {x = negℝ z} {y = negℝ y} {z = x} (≤ℝ-neg {x = y} {y = z} y≤z)

------------------------------------------------------------------------
-- A pair is below the difference two steps ahead
--
-- 配对被两步之后的差所界

-- pair a k = a k - a (k+1) ≤ a k - a (k+2), because decreasing the
-- subtrahend enlarges the difference (sub-anti at dec (suc k)). This is
-- what lets the pairs telescope: summing such differences cancels the
-- interior terms.
--
-- pair a k = a k - a (k+1) ≤ a k - a (k+2)，因为减数变小使差变大
-- （sub-anti 用于 dec (suc k)）。正是这一点让配对可以伸缩：这类差求和
-- 时中间项相互抵消。
pair-le-next : (a : ℕ → RealI) (dec : ∀ n → a (suc n) ≤ℝ a n) (k : ℕ)
             → pair a k ≤ℝ a k -ℝ a (suc (suc k))
pair-le-next a dec k =
  sub-anti (a k) (a (suc (suc k))) (a (suc k)) (dec (suc k))
------------------------------------------------------------------------
-- Two-step advance
--
-- 两步行进

-- twice m n = n + 2 * m, but defined by recursion on m so that the index
-- arithmetic is definitional: twice (suc m) n IS suc (suc (twice m n)).
-- This is what lets the alternating partial sums be analysed in blocks of
-- two without ever rewriting natural-number sums.
--
-- twice m n = n + 2 * m，但按 m 递归定义，使下标算术成为定义性的：
-- twice (suc m) n 就是 suc (suc (twice m n))。正是这一点让交错部分和可以
-- 按两块一组分析，而不必重写下标的自然数加法。
twice : ℕ → ℕ → ℕ
twice zero    n = n
twice (suc m) n = suc (suc (twice m n))

------------------------------------------------------------------------
-- Splitting an alternating sum into a block offset plus pairs
--
-- 把交错和拆成块偏移加配对和

-- alt a (n + 2m) ≈ alt a n + Σ_{j<m} pair a (n + 2j): induction on the
-- number of blocks; the step is one unfolding of alt plus associativity of
-- addition.
--
-- alt a (n + 2m) ≈ alt a n + Σ_{j<m} pair a (n + 2j)：对块数归纳；步例是
-- alt 展开一次加上加法结合律。
alt-split : (a : ℕ → RealI) (n m : ℕ)
          → alt a (twice m n)
            ≈ℝ alt a n +ℝ sum (λ j → pair a (twice j n)) m
alt-split a n zero =
  ≈ℝ-sym (+ℝ-identityʳ (alt a n))
alt-split a n (suc m) =
  ≈ℝ-trans
    (+ℝ-cong (alt-split a n m) ≈ℝ-refl)
    (+ℝ-assoc (alt a n) (sum (λ j → pair a (twice j n)) m)
              (pair a (twice m n)))

------------------------------------------------------------------------
-- Subtracting zero
--
-- 减零

-- x - 0 ≈ x: negℝ 0ℝ ≈ 0ℝ and then the right unit.
--
-- x - 0 ≈ x：negℝ 0ℝ ≈ 0ℝ，再用右单位。
sub-zero : (x : RealI) → x -ℝ 0ℝ ≈ℝ x
sub-zero x =
  ≈ℝ-trans (+ℝ-cong ≈ℝ-refl negℝ-0ℝ) (+ℝ-identityʳ x)

------------------------------------------------------------------------
-- The sum of pairs is below the first omitted term
--
-- 配对之和不超过首个被略去的项

-- Each pair is below the difference spanning two steps (pair-le-next), so
-- the sum of pairs is below the sum of those differences (sum-mono); the
-- latter telescopes to a n - a (n + 2m), which is below a n because the
-- subtrahend is non-negative.
--
-- 每个配对被跨两步的差所界（pair-le-next），故配对之和不超过这些差之和
-- （sum-mono）；后者伸缩成 a n - a (n + 2m)，又因减数非负而低于 a n。
sum-pair-le : (a : ℕ → RealI) (dec : ∀ n → a (suc n) ≤ℝ a n)
              (0≤a : ∀ n → 0ℝ ≤ℝ a n) (n m : ℕ)
            → sum (λ j → pair a (twice j n)) m ≤ℝ a n
sum-pair-le a dec 0≤a n m =
  ≤ℝ-trans
    (≤ℝ-resp-≈ ≈ℝ-refl
      (telescope-sum (λ j → a (twice j n)) m)
      (sum-mono (λ j → pair a (twice j n))
                (λ j → a (twice j n) -ℝ a (twice (suc j) n))
                (λ j → pair-le-next a dec (twice j n)) m))
    (≤ℝ-resp-≈ ≈ℝ-refl (sub-zero (a n))
      (sub-anti (a n) 0ℝ (a (twice m n)) (0≤a (twice m n))))

------------------------------------------------------------------------
-- Remainder bound for the alternating sums
--
-- 交错和的余项界

-- The partial sum at n + 2m is at most alt a n + a n, and at least
-- alt a n. This is the classical Leibniz estimate: the tail after n is
-- bounded by the first omitted term.
--
-- 位于 n + 2m 的部分和不超过 alt a n + a n，且不低于 alt a n。这正是
-- 经典的莱布尼茨估计：n 之后的尾部被首个被略去的项所界。
alt-remainder-le : (a : ℕ → RealI) (dec : ∀ n → a (suc n) ≤ℝ a n)
                   (0≤a : ∀ n → 0ℝ ≤ℝ a n) (n m : ℕ)
                 → alt a (twice m n) ≤ℝ alt a n +ℝ a n
alt-remainder-le a dec 0≤a n m =
  ≤ℝ-resp-≈ (≈ℝ-sym (alt-split a n m)) ≈ℝ-refl
    (≤ℝ-+-monoˡ {x = sum (λ j → pair a (twice j n)) m} {y = a n}
                {z = alt a n} (sum-pair-le a dec 0≤a n m))

alt-remainder-nonNeg : (a : ℕ → RealI) (dec : ∀ n → a (suc n) ≤ℝ a n)
                       (n m : ℕ)
                     → alt a n ≤ℝ alt a (twice m n)
alt-remainder-nonNeg a dec n m =
  ≤ℝ-resp-≈ ≈ℝ-refl (≈ℝ-sym (alt-split a n m))
    (x≤x+y (alt a n) (sum (λ j → pair a (twice j n)) m)
           (sum-nonNeg (λ j → pair a (twice j n))
                       (λ j → pair-nonNeg a dec (twice j n)) m))
