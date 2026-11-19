------------------------------------------------------------------------
-- Exp: the exponential series at the rational level
--
-- Exp：指数级数的有理层
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Core where

open import Data.Nat as Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (m≤m+n; n≤1+n; m+[n∸m]≡n)
  renaming (+-identityʳ to +ℕ-identityʳ; +-suc to +ℕ-suc; +-assoc to +ℕ-assoc
  ; ≤-refl to ≤ℕ-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; NonZero; _≤_; _<_; _+_; _*_; _-_; ∣_∣) renaming (-_ to neg)
open import Data.Rational.Base using (_÷_; 1/_; positive; Positive; nonNegative)
open import Data.Rational.Properties using
  (≤-refl; <⇒≤; *-zeroʳ; +-identityˡ; +-identityʳ; +-mono-≤; +-monoʳ-≤
  ; +-assoc; *-assoc; *-comm; *-identityˡ; *-identityʳ; *-inverseˡ
  ; *-monoˡ-≤-nonNeg; *-cancelʳ-≤-pos; pos*pos⇒pos; ≤-trans; ≤-<-trans
  ; *-distribˡ-+; +-comm; +-monoˡ-≤; ∣p∣≡p∨∣p∣≡-p; 1/pos⇒pos
  ; pos⇒nonZero; positive⁻¹)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Base.RationalRing using (neg-sub)
open import Real using
  (embed; 0<embed; 2ℚ; half; ε; 0<ε; embed-mono-≤; CauchySeq)
open import Real.CauchyToInterval using (cauchy→realI)
open import Real.IntervalEquiv using (bound-w; recipPow2)
open import Real.Interval using (RealI)
open import Real.Interval.Complete using (ε-half<)
open import Real.Interval.Kit using
  (*-mono-≤-nonNeg; 2ℚ*half≡1; 0≤half; 0<half; 0≤recipPow2; recipPow2-mul
  ; tail-bound; 0≤diff)
open import Real.Interval.Series.Bounds using
  (recipPow2-suc; geom; geom-le; geom-nonNeg; le-self-add)
open import Real.Interval.ContinuityMul using (le-shift-sub)

infix 4 _≤ℕ_
_≤ℕ_ : ℕ → ℕ → Set
_≤ℕ_ m n = Nat._≤_ m n

------------------------------------------------------------------------
-- The increment denominators are non-zero
--
-- 增量分母非零

-- The exponential of a rational is the sum of its series
--     exp q = Σ_k q^k / k!
-- and this module defines the terms by the standard recurrence
--     term q 0 = 1,   term q (k+1) = term q k * (q / (k+1))
-- which is exactly the factorial scaling in one step. The closed form
--     term q k = q^k / k!
-- is a proposition about this recurrence, not a definition: stdlib has no
-- algebra for rational division (Data.Rational.Properties contains no ÷
-- law at all), so the equivalence would cost a quotient-algebra module of
-- its own, while the recurrence already carries the two facts the later
-- slices use. Those two facts are the monotonicity of the partial sums and
-- their non-negativity, both proved here.
-- The tail control (the ratio q / (k+1) eventually at most a half, hence
-- a geometric bound by recipPow2, hence an arbitrarily narrow bracket) is
-- the next slice; it consumes exactly the recurrence proved as `term-suc`
-- below.
--     exp q = Σ_k q^k / k!
--     term q 0 = 1,   term q (k+1) = term q k * (q / (k+1))
--     term q k = q^k / k!
-- Every k+1 embeds to a positive, hence non-zero, rational; without this
-- the term would be a partial operation.
--
-- 有理数的指数是其级数之和
-- 本模块用标准的通项递推来定义
-- 这正是阶乘缩放的一步。闭式
-- 是关于该递推的命题，而非定义：stdlib 没有任何有理除法的代数
-- （Data.Rational.Properties 里 ÷ 的定律零命中），故等价性要另付一个
-- 商代数的模块，而递推本身已经携带后续切片需要的两条事实。这两条是
-- 部分和的单调性与非负性，均在此证出。
-- 尾部控制（比值 q / (k+1) 最终不超过一半，于是由 recipPow2 给出几何界，
-- 于是得到任意窄的 bracket）是下一个切片；它恰好消耗下面作为 `term-suc`
-- 证出的递推。
-- 每个 k+1 嵌入为正，故非零的有理数；否则通项就是偏运算。
sucNonZero : (k : ℕ) → NonZero (embed (suc k))
sucNonZero k = pos⇒nonZero (embed (suc k)) {{positive (0<embed k)}}

------------------------------------------------------------------------
-- Terms of the exponential series
--
-- 指数级数的通项

-- term q 0 = 1, term q (k+1) = term q k * (q / (k+1)). The recurrence is
-- definitional, which is the whole point: the halving step of the tail
-- estimate is one unfolding, with no quotient algebra in between.
--
-- term q 0 = 1，term q (k+1) = term q k * (q / (k+1))。递推是定义性的，
-- 这正是关键：尾部估计的减半步骤只需一次展开，中间不出现商代数。
term : ℚ → ℕ → ℚ
term q zero    = 1ℚ
term q (suc k) = term q k * _÷_ q (embed (suc k)) {{sucNonZero k}}

term-suc : (q : ℚ) (k : ℕ)
         → term q (suc k) ≡ term q k * _÷_ q (embed (suc k)) {{sucNonZero k}}
term-suc q k = refl

------------------------------------------------------------------------
-- Dividing by a positive increment keeps a non-negative value
--
-- 除以正的增量保持非负

-- p / (k+1) unfolds to p * (1 / (k+1)); the reciprocal of a positive is
-- positive, and a product of two non-negatives is non-negative.
--
-- p / (k+1) 展开为 p * (1 / (k+1))；正数的倒数为正，两个非负之积非负。
div-suc-nonNeg : (p : ℚ) (0≤p : 0ℚ ≤ p) (k : ℕ)
               → 0ℚ ≤ _÷_ p (embed (suc k)) {{sucNonZero k}}
div-suc-nonNeg p 0≤p k =
  subst (λ z → z ≤ p * (1/_ (embed (suc k)) {{sucNonZero k}})) (*-zeroʳ 0ℚ)
    (*-mono-≤-nonNeg {a = 0ℚ} {a' = p} {b = 0ℚ}
                      {b' = 1/_ (embed (suc k)) {{sucNonZero k}}}
      (≤-refl {0ℚ}) 0≤p (≤-refl {0ℚ})
      (<⇒≤ (positive⁻¹ (1/_ (embed (suc k)) {{sucNonZero k}})
             {{1/pos⇒pos (embed (suc k)) {{positive (0<embed k)}}}})))

------------------------------------------------------------------------
-- Terms are non-negative for non-negative arguments
--
-- 非负自变量的通项非负

-- Induction on k: the first term is 1, and each step multiplies a
-- non-negative value by a non-negative increment quotient.
--
-- 对 k 归纳：首项为 1，每一步把非负值乘以非负的增量商。
term-nonNeg : (q : ℚ) (0≤q : 0ℚ ≤ q) (k : ℕ) → 0ℚ ≤ term q k
term-nonNeg q 0≤q zero    = <⇒≤ (0<embed zero)
term-nonNeg q 0≤q (suc k) =
  subst (λ z → z ≤ term q k * (_÷_ q (embed (suc k)) {{sucNonZero k}}))
    (*-zeroʳ 0ℚ)
    (*-mono-≤-nonNeg {a = 0ℚ} {a' = term q k} {b = 0ℚ}
                      {b' = _÷_ q (embed (suc k)) {{sucNonZero k}}}
      (≤-refl {0ℚ}) (term-nonNeg q 0≤q k) (≤-refl {0ℚ})
      (div-suc-nonNeg q 0≤q k))

------------------------------------------------------------------------
-- Partial sums
--
-- 部分和

sumQ : (ℕ → ℚ) → ℕ → ℚ
sumQ f zero    = 0ℚ
sumQ f (suc m) = sumQ f m + f m

expPartial : ℚ → ℕ → ℚ
expPartial q = sumQ (term q)

expPartial-zero : (q : ℚ) → expPartial q zero ≡ 0ℚ
expPartial-zero q = refl

expPartial-suc : (q : ℚ) (m : ℕ)
               → expPartial q (suc m) ≡ expPartial q m + term q m
expPartial-suc q m = refl

------------------------------------------------------------------------
-- Partial sums of non-negative terms are non-negative
--
-- 非负项的部分和非负

sumQ-nonNeg : (f : ℕ → ℚ) (0≤f : ∀ k → 0ℚ ≤ f k) (m : ℕ) → 0ℚ ≤ sumQ f m
sumQ-nonNeg f 0≤f zero    = ≤-refl
sumQ-nonNeg f 0≤f (suc m) =
  subst (λ z → z ≤ sumQ f m + f m) (+-identityˡ 0ℚ)
    (+-mono-≤ (sumQ-nonNeg f 0≤f m) (0≤f m))

------------------------------------------------------------------------
-- Each new term raises the partial sum
--
-- 每加一项部分和上升

-- sumQ f m ≤ sumQ f (suc m) whenever the new term is non-negative:
-- right-addition monotonicity, then forgetting the zero on the left.
--
-- 只要新项非负就有 sumQ f m ≤ sumQ f (suc m)：右加单调，再把左边的零去掉。
sumQ-step-mono : (f : ℕ → ℚ) (0≤f : ∀ k → 0ℚ ≤ f k) (m : ℕ)
               → sumQ f m ≤ sumQ f (suc m)
sumQ-step-mono f 0≤f m =
  subst (λ z → z ≤ sumQ f m + f m) (+-identityʳ (sumQ f m))
    (+-monoʳ-≤ (sumQ f m) (0≤f m))

------------------------------------------------------------------------
-- The exponential partial sums are non-negative and increasing
--
-- 指数部分和非负且递增

expPartial-nonNeg : (q : ℚ) (0≤q : 0ℚ ≤ q) (m : ℕ)
                  → 0ℚ ≤ expPartial q m
expPartial-nonNeg q 0≤q = sumQ-nonNeg (term q) (term-nonNeg q 0≤q)

expPartial-step-mono : (q : ℚ) (0≤q : 0ℚ ≤ q) (m : ℕ)
                    → expPartial q m ≤ expPartial q (suc m)
expPartial-step-mono q 0≤q = sumQ-step-mono (term q) (term-nonNeg q 0≤q)

------------------------------------------------------------------------
-- The increment quotient is at most a half past the threshold
--
-- 越过阈值后增量商不超过一半

-- If 2q ≤ s then q / s ≤ 1/2. stdlib has no order law for division, so
-- this goes by cross-multiplication with the positive factor 2*s: the
-- left side then collapses to 2q through (1/s)*s ≡ 1, the right side to
-- s through half*2 ≡ 1, and positivity allows cancelling 2*s again.
--
-- 若 2q ≤ s，则 q / s ≤ 1/2。stdlib 没有除法序律，故走与正因子 2*s 的
-- 交叉相乘：左端经 (1/s)*s ≡ 1 塌成 2q，右端经 half*2 ≡ 1 塌成 s，再凭
-- 2*s 的正性把它约掉。
inv-s-mul : (s : ℚ) {{_ : Positive s}}
          → (1/_ s) {{pos⇒nonZero s}} * (2ℚ * s) ≡ 2ℚ
inv-s-mul s =
  let nz = pos⇒nonZero s
      r  = 1/_ s {{nz}}
  in trans (sym (*-assoc r 2ℚ s))
  (trans (cong (λ z → z * s) (*-comm r 2ℚ))
  (trans (*-assoc 2ℚ r s)
  (trans (cong (2ℚ *_) (*-inverseˡ s {{nz}})) (*-identityʳ 2ℚ))))

half-mul-two : half * 2ℚ ≡ 1ℚ
half-mul-two = trans (*-comm half 2ℚ) 2ℚ*half≡1

div-le-half : (q s : ℚ) {{_ : Positive s}} → 2ℚ * q ≤ s
            → _÷_ q s {{pos⇒nonZero s}} ≤ half
div-le-half q s 2q≤s =
  let nz = pos⇒nonZero s
      r  = 1/_ s {{nz}}
      A : (q * r) * (2ℚ * s) ≡ 2ℚ * q
      A = trans (*-assoc q r (2ℚ * s))
            (trans (cong (q *_) (inv-s-mul s)) (*-comm q 2ℚ))
      B : half * (2ℚ * s) ≡ s
      B = trans (sym (*-assoc half 2ℚ s))
            (trans (cong (λ z → z * s) half-mul-two) (*-identityˡ s))
  in *-cancelʳ-≤-pos (2ℚ * s) {{pos*pos⇒pos 2ℚ s}}
       (subst (λ z → z ≤ half * (2ℚ * s)) (sym A)
         (subst (λ z → 2ℚ * q ≤ z) (sym B) 2q≤s))

------------------------------------------------------------------------
-- The terms at least halve past the threshold
--
-- 越过阈值后通项至少减半

-- term q (k+1) = term q k * (q / (k+1)); the quotient is at most a half
-- by the lemma above, and multiplying on the left by the non-negative
-- term q k preserves the order.
--
-- term q (k+1) = term q k * (q / (k+1))；由上面的引理商不超过一半，再用
-- 非负的 term q k 左乘保持序。
term-halve : (q : ℚ) (0≤q : 0ℚ ≤ q) (k : ℕ)
           → 2ℚ * q ≤ embed (suc k)
           → term q (suc k) ≤ term q k * half
term-halve q 0≤q k 2q≤s =
  subst (λ z → z ≤ term q k * half) (sym (term-suc q k))
    (*-monoˡ-≤-nonNeg (term q k) {{nonNegative (term-nonNeg q 0≤q k)}}
      (div-le-half q (embed (suc k)) {{positive (0<embed k)}} 2q≤s))
------------------------------------------------------------------------
-- A threshold past which two q fits under the increment denominator
--
-- 存在阈值使 2q 落在增量分母之下

-- The rational archimedean property (bound-w) puts M above 2q, and
-- embed-mono-≤ carries that bound up to every k ≥ M and then one step
-- further to k+1.
--
-- 有理阿基米德性（bound-w）给出 M 在 2q 之上，embed-mono-≤ 把这个界抬到
-- 每个 k ≥ M，并再抬一步到 k+1。
two-q-nonNeg : (q : ℚ) (0≤q : 0ℚ ≤ q) → 0ℚ ≤ 2ℚ * q
two-q-nonNeg q 0≤q =
  subst (λ z → z ≤ 2ℚ * q) (*-zeroʳ 0ℚ)
    (*-mono-≤-nonNeg {a = 0ℚ} {a' = 2ℚ} {b = 0ℚ} {b' = q}
      (≤-refl {0ℚ}) (<⇒≤ (0<embed (suc zero))) (≤-refl {0ℚ}) 0≤q)

halve-threshold : (q : ℚ) (0≤q : 0ℚ ≤ q)
                → Σ ℕ (λ n₀ → ∀ k → n₀ ≤ℕ k → 2ℚ * q ≤ embed (suc k))
halve-threshold q 0≤q =
  let M , 2q≤M = bound-w (2ℚ * q) (two-q-nonNeg q 0≤q)
  in M , (λ k M≤k
          → ≤-trans 2q≤M
              (≤-trans (embed-mono-≤ {m = M} {n = k} M≤k)
                       (embed-mono-≤ {m = k} {n = suc k} (n≤1+n k))))

------------------------------------------------------------------------
-- Beyond the threshold the terms are geometric with ratio a half
--
-- 越过阈值后通项是公比一半的几何项

-- Induction on j: at j = 0 the bound is reflexivity after forgetting the
-- factor 1 on the right; the step halves the term and reassociates
-- recipPow2 j * half into recipPow2 (j+1).
--
-- 对 j 归纳：j = 0 时右侧因子 1 去掉即自反；步例把通项减半，再把
-- recipPow2 j * half 重结成 recipPow2 (j+1)。
term-geo : (q : ℚ) (0≤q : 0ℚ ≤ q) (n₀ : ℕ)
         → (∀ k → n₀ ≤ℕ k → 2ℚ * q ≤ embed (suc k))
         → (j : ℕ) → term q (n₀ +ℕ j) ≤ term q n₀ * recipPow2 j
term-geo q 0≤q n₀ H zero =
  subst (λ z → term q z ≤ term q n₀ * recipPow2 zero) (sym (+ℕ-identityʳ n₀))
    (subst (λ z → term q n₀ ≤ z) (sym (*-identityʳ (term q n₀)))
      (≤-refl {term q n₀}))
term-geo q 0≤q n₀ H (suc j) =
  let step : term q (suc (n₀ +ℕ j)) ≤ term q (n₀ +ℕ j) * half
      step = term-halve q 0≤q (n₀ +ℕ j) (H (n₀ +ℕ j) (m≤m+n n₀ j))
      ih = term-geo q 0≤q n₀ H j
      mono : term q (n₀ +ℕ j) * half ≤ (term q n₀ * recipPow2 j) * half
      mono = *-mono-≤-nonNeg {a = term q (n₀ +ℕ j)}
               {a' = term q n₀ * recipPow2 j}
               {b = half} {b' = half}
               (term-nonNeg q 0≤q (n₀ +ℕ j)) ih 0≤half (≤-refl {half})
      E : (term q n₀ * recipPow2 j) * half ≡ term q n₀ * recipPow2 (suc j)
      E = trans (*-assoc (term q n₀) (recipPow2 j) half)
            (cong (term q n₀ *_) (sym (recipPow2-suc j)))
      core : term q (suc (n₀ +ℕ j)) ≤ term q n₀ * recipPow2 (suc j)
      core = ≤-trans step
               (subst (λ z → term q (n₀ +ℕ j) * half ≤ z) E mono)
  in subst (λ z → term q z ≤ term q n₀ * recipPow2 (suc j))
       (sym (+ℕ-suc n₀ j)) core
------------------------------------------------------------------------
-- The tail of the exponential series is arbitrarily narrow
--
-- 指数级数的尾部任意窄

-- Threshold n₀ makes every later term at most half of its predecessor;
-- from there the terms are dominated by term q n₀ * recipPow2, so a tail
-- starting at n₀ + N₀ is bounded by (2 * term q n₀) * recipPow2 N₀,
-- uniformly in its length, by the geometric mass being at most two. Kit's
-- tail-bound then picks N₀ that pushes this bound under any given d.
--
-- 阈值 n₀ 让之后每项不超过前项一半；由此通项被 term q n₀ * recipPow2 支配，
-- 故从 n₀ + N₀ 起的尾部不论多长都不超过 (2 * term q n₀) * recipPow2 N₀，
-- 依据是几何质量不超过二。随后 Kit 的 tail-bound 给出把该界压到任意 d
-- 之下的 N₀。
sumQ-cong : (f g : ℕ → ℚ) (e : ∀ i → f i ≡ g i) (m : ℕ) → sumQ f m ≡ sumQ g m
sumQ-cong f g e zero    = refl
sumQ-cong f g e (suc m) = cong₂ _+_ (sumQ-cong f g e m) (e m)

sumQ-mono : (f g : ℕ → ℚ) (h : ∀ i → f i ≤ g i) (m : ℕ) → sumQ f m ≤ sumQ g m
sumQ-mono f g h zero    = ≤-refl
sumQ-mono f g h (suc m) = +-mono-≤ (sumQ-mono f g h m) (h m)

sumQ-scaled : (c : ℚ) (m : ℕ) → sumQ (λ i → c * recipPow2 i) m ≡ c * geom m
sumQ-scaled c zero    = sym (*-zeroʳ c)
sumQ-scaled c (suc m) =
  trans (cong₂ _+_ (sumQ-scaled c m) refl)
        (sym (*-distribˡ-+ c (geom m) (recipPow2 m)))

term-geo-shift : (q : ℚ) (0≤q : 0ℚ ≤ q) (n₀ : ℕ)
                 (H : ∀ k → n₀ ≤ℕ k → 2ℚ * q ≤ embed (suc k))
                 (N₀ : ℕ) (i : ℕ)
               → term q (n₀ +ℕ (N₀ +ℕ i))
                 ≤ (term q n₀ * recipPow2 N₀) * recipPow2 i
term-geo-shift q 0≤q n₀ H N₀ i =
  let g = term-geo q 0≤q n₀ H (N₀ +ℕ i)
      A : term q n₀ * recipPow2 (N₀ +ℕ i)
          ≡ (term q n₀ * recipPow2 N₀) * recipPow2 i
      A = trans (cong (term q n₀ *_) (recipPow2-mul N₀ i))
            (sym (*-assoc (term q n₀) (recipPow2 N₀) (recipPow2 i)))
  in subst (λ z → term q (n₀ +ℕ (N₀ +ℕ i)) ≤ z) A g

two-term-nonNeg : (q : ℚ) (0≤q : 0ℚ ≤ q) (n₀ : ℕ) → 0ℚ ≤ 2ℚ * term q n₀
two-term-nonNeg q 0≤q n₀ =
  subst (λ z → z ≤ 2ℚ * term q n₀) (*-zeroʳ 0ℚ)
    (*-mono-≤-nonNeg {a = 0ℚ} {a' = 2ℚ} {b = 0ℚ} {b' = term q n₀}
      (≤-refl {0ℚ}) (<⇒≤ (0<embed (suc zero))) (≤-refl {0ℚ})
      (term-nonNeg q 0≤q n₀))

exp-tail-geo : (q : ℚ) (0≤q : 0ℚ ≤ q) (n₀ : ℕ)
               (H : ∀ k → n₀ ≤ℕ k → 2ℚ * q ≤ embed (suc k))
               (N₀ : ℕ) (m : ℕ)
             → sumQ (λ i → term q (n₀ +ℕ (N₀ +ℕ i))) m
               ≤ (2ℚ * term q n₀) * recipPow2 N₀
exp-tail-geo q 0≤q n₀ H N₀ m =
  let c = term q n₀ * recipPow2 N₀
      0≤c : 0ℚ ≤ c
      0≤c = subst (λ z → z ≤ c) (*-zeroʳ 0ℚ)
              (*-mono-≤-nonNeg {a = 0ℚ} {a' = term q n₀} {b = 0ℚ}
                                {b' = recipPow2 N₀}
                (≤-refl {0ℚ}) (term-nonNeg q 0≤q n₀) (≤-refl {0ℚ})
                (0≤recipPow2 N₀))
      step1 : sumQ (λ i → term q (n₀ +ℕ (N₀ +ℕ i))) m ≤ c * geom m
      step1 = ≤-trans (sumQ-mono (λ i → term q (n₀ +ℕ (N₀ +ℕ i)))
                                 (λ i → c * recipPow2 i)
                                 (term-geo-shift q 0≤q n₀ H N₀) m)
                (subst (λ z → sumQ (λ i → c * recipPow2 i) m ≤ z)
                       (sumQ-scaled c m) (≤-refl {sumQ (λ i → c * recipPow2 i) m}))
      step2 : c * geom m ≤ c * 2ℚ
      step2 = *-mono-≤-nonNeg {a = c} {a' = c} {b = geom m} {b' = 2ℚ}
               0≤c (≤-refl {c}) (geom-nonNeg m) (geom-le m)
      step3 : c * 2ℚ ≡ (2ℚ * term q n₀) * recipPow2 N₀
      step3 = trans (*-comm c 2ℚ)
                (sym (*-assoc 2ℚ (term q n₀) (recipPow2 N₀)))
  in ≤-trans step1 (≤-trans step2
       (subst (λ z → c * 2ℚ ≤ z) step3 (≤-refl {c * 2ℚ})))

exp-tail : (q : ℚ) (0≤q : 0ℚ ≤ q) (d : ℚ) (0<d : 0ℚ < d)
         → Σ ℕ (λ N → ∀ m → sumQ (λ i → term q (N +ℕ i)) m < d)
exp-tail q 0≤q d 0<d =
  let n₀ , H = halve-threshold q 0≤q
      C = 2ℚ * term q n₀
      0≤C = two-term-nonNeg q 0≤q n₀
      N₀ , hN₀ = tail-bound C 0≤C d 0<d
  in n₀ +ℕ N₀ , (λ m
     → let e : sumQ (λ i → term q (n₀ +ℕ (N₀ +ℕ i))) m
               ≡ sumQ (λ i → term q ((n₀ +ℕ N₀) +ℕ i)) m
           e = sumQ-cong (λ i → term q (n₀ +ℕ (N₀ +ℕ i)))
                         (λ i → term q ((n₀ +ℕ N₀) +ℕ i))
                         (λ i → cong (term q) (sym (+ℕ-assoc n₀ N₀ i))) m
       in subst (λ z → z < d) e
            (≤-<-trans (exp-tail-geo q 0≤q n₀ H N₀ m)
                       (hN₀ N₀ ≤ℕ-refl)))
------------------------------------------------------------------------
-- Bracket width of a rational exponential
--
-- 有理指数函数值的括号宽度

-- sumQ-split turns a longer partial sum into a prefix plus a tail, so
-- monotonicity of the partial sums reduces to non-negativity of terms,
-- and the tail estimate exp-tail bounds the long partial sums from above
-- by the prefix plus d. Both halves together say the bracket
-- [expPartial q N, expPartial q N + d] swallows every later partial sum
-- and the next bracket, which is what a nested bracket needs.
--
-- sumQ-split 把较长的部分和拆成前缀加尾段，于是部分和的单调性归约为通项
-- 非负，而尾部估计 exp-tail 从上方给出"较长部分和不超过前缀加 d"。两半
-- 合起来即：括号 [expPartial q N, expPartial q N + d] 吞掉之后的一切部分和，
-- 这正是嵌套括号所需。
sumQ-split : (f : ℕ → ℚ) (n d : ℕ)
           → sumQ f (n +ℕ d) ≡ sumQ f n + sumQ (λ i → f (n +ℕ i)) d
sumQ-split f n zero =
  trans (cong (sumQ f) (+ℕ-identityʳ n)) (sym (+-identityʳ (sumQ f n)))
sumQ-split f n (suc d) =
  let A : sumQ f (n +ℕ suc d) ≡ sumQ f (suc (n +ℕ d))
      A = cong (sumQ f) (+ℕ-suc n d)
      C : sumQ f (n +ℕ d) ≡ sumQ f n + sumQ (λ i → f (n +ℕ i)) d
      C = sumQ-split f n d
      D : sumQ (λ i → f (n +ℕ i)) (suc d)
          ≡ sumQ (λ i → f (n +ℕ i)) d + f (n +ℕ d)
      D = refl
  in trans A
       (trans (cong₂ _+_ C refl)
         (trans (+-assoc (sumQ f n) (sumQ (λ i → f (n +ℕ i)) d) (f (n +ℕ d)))
           (cong (sumQ f n +_) (sym D))))

expPartial-mono : (q : ℚ) (0≤q : 0ℚ ≤ q) (n d : ℕ)
                → expPartial q n ≤ expPartial q (n +ℕ d)
expPartial-mono q 0≤q n zero =
  subst (λ z → expPartial q n ≤ z)
    (sym (cong (expPartial q) (+ℕ-identityʳ n))) (≤-refl {expPartial q n})
expPartial-mono q 0≤q n (suc d) =
  let A : expPartial q (n +ℕ suc d)
          ≡ expPartial q (n +ℕ d) + term q (n +ℕ d)
      A = trans (cong (expPartial q) (+ℕ-suc n d)) refl
      step : expPartial q (n +ℕ d) ≤ expPartial q (n +ℕ suc d)
      step = subst (λ z → expPartial q (n +ℕ d) ≤ z) (sym A)
               (le-self-add (term-nonNeg q 0≤q (n +ℕ d)))
  in ≤-trans (expPartial-mono q 0≤q n d) step

exp-bracket : (q : ℚ) (0≤q : 0ℚ ≤ q) (d : ℚ) (0<d : 0ℚ < d)
            → Σ ℕ (λ N → ∀ j
                → (expPartial q N ≤ expPartial q (N +ℕ j))
                × (expPartial q (N +ℕ j) ≤ expPartial q N + d))
exp-bracket q 0≤q d 0<d =
  let N , hN = exp-tail q 0≤q d 0<d
  in N , (λ j
     → let S = sumQ (λ i → term q (N +ℕ i)) j
           H : expPartial q N + S ≡ expPartial q (N +ℕ j)
           H = sym (sumQ-split (term q) N j)
           second : expPartial q (N +ℕ j) ≤ expPartial q N + d
           second = subst (λ z → z ≤ expPartial q N + d) H
                      (+-monoʳ-≤ (expPartial q N) (<⇒≤ (hN j)))
       in expPartial-mono q 0≤q N j , second)
------------------------------------------------------------------------
-- The rational exponential partial sums are Cauchy
--
-- 有理指数部分和是柯西列

-- Bracket nesting gives one common index N beyond which every partial
-- sum stays inside [a N, a N + d]. Two such sums therefore differ by at
-- most d in either direction, so the absolute value is bounded by d; with
-- d = ε k * half and ε-half< the bound is strict at ε k. The subtraction
-- lemmas are stated in the "move the subtracted term over" form
-- (p - q ≤ r follows from p ≤ r + q), because ℚ has no division laws and
-- no negation monotonicity for ≤.
-- The statement is the same as Real.Interval.ContinuityMul.le-shift-sub up
-- to commuting the two summands on the right, and is forwarded with that
-- single commutation.
--
-- 括号嵌套给出一个共同指标 N，之后一切部分和都留在 [a N, a N + d] 内。
-- 于是两个这样的和两个方向都相差不超过 d，绝对值也被 d 界定；取
-- d = ε k * half，再用 ε-half< 即得对 ε k 的严格界。减法引理都写成
-- "把被减项移到另一边"的形式（由 p ≤ r + q 得 p - q ≤ r），因为 ℚ 没有
-- 除法定律、也没有 ≤ 的取负单调性。
-- 该陈述与 Real.Interval.ContinuityMul.le-shift-sub 只差右侧两个加项的
-- 次序，交换后直接转发。
sub-le-shift : (p q r : ℚ) → p ≤ r + q → p - q ≤ r
sub-le-shift p q r h = le-shift-sub p q r (subst (λ z → p ≤ z) (+-comm r q) h)

sub-nonNeg : (p q : ℚ) → p ≤ q → 0ℚ ≤ q - p
sub-nonNeg p q p≤q = 0≤diff {p} {q} p≤q

abs-le : (p q : ℚ) → p ≤ q → neg p ≤ q → ∣ p ∣ ≤ q
abs-le p q p≤q np≤q with ∣p∣≡p∨∣p∣≡-p p
... | inj₁ e = subst (λ z → z ≤ q) (sym e) p≤q
... | inj₂ e = subst (λ z → z ≤ q) (sym e) np≤q

expPartial-le : (q : ℚ) (0≤q : 0ℚ ≤ q) (n m : ℕ) → n ≤ℕ m
              → expPartial q n ≤ expPartial q m
expPartial-le q 0≤q n m n≤m =
  subst (λ z → expPartial q n ≤ expPartial q z)
    (m+[n∸m]≡n {n} {m} n≤m)
    (expPartial-mono q 0≤q n (m ∸ n))

exp-bracket-le : (q : ℚ) (0≤q : 0ℚ ≤ q) (d : ℚ) (0<d : 0ℚ < d)
               → Σ ℕ (λ N
                   → (∀ m → N ≤ℕ m → expPartial q N ≤ expPartial q m)
                   × (∀ m → N ≤ℕ m → expPartial q m ≤ expPartial q N + d))
exp-bracket-le q 0≤q d 0<d =
  let N , br = exp-bracket q 0≤q d 0<d
  in N , ( (λ m m≥ → expPartial-le q 0≤q N m m≥)
         , (λ m m≥ →
              let e : N +ℕ (m ∸ N) ≡ m
                  e = m+[n∸m]≡n {N} {m} m≥
              in subst (λ z → expPartial q z ≤ expPartial q N + d) e
                   (proj₂ (br (m ∸ N))) ) )

expPartial-cauchy-half : (q : ℚ) (0≤q : 0ℚ ≤ q) (d : ℚ) (0<d : 0ℚ < d)
                       → Σ ℕ (λ N → ∀ n m → N ≤ℕ n → N ≤ℕ m
                           → ∣ expPartial q n - expPartial q m ∣ ≤ d)
expPartial-cauchy-half q 0≤q d 0<d =
  let N , (upperN , belowN) = exp-bracket-le q 0≤q d 0<d
  in N , (λ n m n≥ m≥ →
       let an≤d+am : expPartial q n ≤ d + expPartial q m
           an≤d+am = ≤-trans (belowN n n≥)
                       (subst (λ z → expPartial q N + d ≤ z)
                              (+-comm (expPartial q m) d)
                              (+-monoˡ-≤ d (upperN m m≥)))
           am≤d+an : expPartial q m ≤ d + expPartial q n
           am≤d+an = ≤-trans (belowN m m≥)
                       (subst (λ z → expPartial q N + d ≤ z)
                              (+-comm (expPartial q n) d)
                              (+-monoˡ-≤ d (upperN n n≥)))
           bound1 : expPartial q n - expPartial q m ≤ d
           bound1 = sub-le-shift (expPartial q n) (expPartial q m) d an≤d+am
           bound2 : neg (expPartial q n - expPartial q m) ≤ d
           bound2 = subst (λ z → z ≤ d)
                     (sym (neg-sub (expPartial q n) (expPartial q m)))
                     (sub-le-shift (expPartial q m) (expPartial q n) d am≤d+an)
       in abs-le (expPartial q n - expPartial q m) d bound1 bound2)

expPartial-cauchy : (q : ℚ) (0≤q : 0ℚ ≤ q) (k : ℕ)
                  → Σ ℕ (λ N → ∀ n m → N ≤ℕ n → N ≤ℕ m
                      → ∣ expPartial q n - expPartial q m ∣ < ε k)
expPartial-cauchy q 0≤q k =
  let d = ε k * half
      0<d : 0ℚ < d
      0<d = positive⁻¹ d
              {{pos*pos⇒pos (ε k) {{positive (0<ε k)}} half {{positive 0<half}}}}
      N , h = expPartial-cauchy-half q 0≤q d 0<d
  in N , (λ n m n≥ m≥ → ≤-<-trans (h n m n≥ m≥) (ε-half< k))
------------------------------------------------------------------------
-- The exponential of a non-negative rational
--
-- 非负有理数的指数

-- The partial sums form a CauchySeq in the repo's sense, so the
-- completion bridge turns them into a RealI. No bracket nesting is
-- needed here: the sequence of rationals is itself the object, and
-- cauchy→realI rebuilds the intervals from it.
--
-- 部分和按全仓意义的 CauchySeq 构成柯西列，故完备性桥把它变成 RealI。
-- 这里不需要外层括号嵌套：有理序列本身就是对象，cauchy→realI 由它重建区间。
expSeq : (q : ℚ) (0≤q : 0ℚ ≤ q) → CauchySeq
expSeq q 0≤q = record
  { f      = λ n → expPartial q n
  ; μ      = λ k → proj₁ (expPartial-cauchy q 0≤q k)
  ; cauchy = λ k n m n≥ m≥ → proj₂ (expPartial-cauchy q 0≤q k) n m n≥ m≥
  }

expq : (q : ℚ) → 0ℚ ≤ q → RealI
expq q 0≤q = cauchy→realI (expSeq q 0≤q)
