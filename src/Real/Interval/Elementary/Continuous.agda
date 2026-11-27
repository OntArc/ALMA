------------------------------------------------------------------------
-- Continuity of the truncated exponential series in its point
--
-- 截断指数级数关于其取点的连续性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Elementary.Continuous where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; [_,_]′)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _⊓_; _*_; _≤_; _<_; _-_; Positive; positive)
  renaming (-_ to neg)
open import Data.Rational.Properties using
  ( p⊓q≤p; p⊓q≤q; ⊓-sel; *-identityʳ; *-monoʳ-<-pos; pos*pos⇒pos
  ; positive⁻¹; <-≤-trans; +-monoˡ-<; +-inverseʳ; +-comm; <⇒≤)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import Real using (ε; 0<ε; half; embed; 0<embed)
open import Real.Archimedean using (ε-archimedean)
open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ; 1ℝ; _+ℝ_; _-ℝ_; negℝ)
open import Real.Interval.ArithLaws using
  (+ℝ-identityʳ; +ℝ-identityˡ; +ℝ-inverseʳ; negℝ-0ℝ; +ℝ-comm; sub-add-cancelℝ)
open import Real.Interval.Continuity using
  ( Close; close-mono; Close-self; continuous-+-at; 0<embedℚ; embedℚ-mono
  ; sub-add-cancel)
open import Real.Interval.ContinuityProd using (continuous-*-at)
open import Real.Interval.ContinuityClose using (close-left)
open import Real.Interval.DensityArch using (dense)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-trans; ≈ℝ-sym)
open import Real.Interval.Embed using (embedℚ-+)
open import Real.Interval.Exp.Series using (termℝ; expPartialℝ)
open import Real.Interval.Kit using (0<half)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Order using (≈-<-respʳ)
open import Real.Interval.OrderLaws using (half<1; <-+mono; ≈-<-resp)
open import Real.Interval.OrderLe using (<-+mono-reflect; sub-pos-lt)
open import Real.Interval.Order using (_<ℝ_) renaming (<-trans to <-transR)
open import Real.Interval.Sqrt.Bounds using (embedℚ-reflect)
open import Real.Interval.Rational using (pos-diff)
open import Real.Interval.Recip using (recipℝ)

------------------------------------------------------------------------
-- A positive radius strictly below two given positive radii
--
-- 严格小于两个给定正半径的正半径

-- Given two positive radii, produce a positive one strictly below both
-- The value is half of the minimum, so that both strict comparisons
-- follow from `half < 1` rather than from an appeal to trichotomy.
--
-- 给定两个正半径，产出一个严格小于两者的正半径
-- 取最小者的一半，使两个严格比较都由 `half < 1` 得到，而不必诉诸三歧性。
radius-refine : (d₁ d₂ : ℚ) → 0ℚ < d₁ → 0ℚ < d₂
              → Σ ℚ (λ d → (0ℚ < d) × ((d < d₁) × (d < d₂)))
radius-refine d₁ d₂ 0<d₁ 0<d₂ =
  let
    m : ℚ
    m = d₁ ⊓ d₂

    0<m : 0ℚ < m
    0<m = [ (λ e → subst (λ z → 0ℚ < z) (sym e) 0<d₁)
          , (λ e → subst (λ z → 0ℚ < z) (sym e) 0<d₂) ]′ (⊓-sel d₁ d₂)

    m≤d₁ : m ≤ d₁
    m≤d₁ = p⊓q≤p d₁ d₂

    m≤d₂ : m ≤ d₂
    m≤d₂ = p⊓q≤q d₁ d₂

    d : ℚ
    d = m * half

    0<d : 0ℚ < d
    0<d = positive⁻¹ d {{pos*pos⇒pos m {{positive 0<m}} half {{positive 0<half}}}}

    d<m : d < m
    d<m = subst (λ z → m * half < z) (*-identityʳ m)
            (*-monoʳ-<-pos m {{positive 0<m}} half<1)
  in d , (0<d , (<-≤-trans d<m m≤d₁ , <-≤-trans d<m m≤d₂))

------------------------------------------------------------------------
-- Constant functions are continuous
--
-- 常值函数连续

-- Every constant function is continuous at every point, at every level
-- The modulus is the level's own `ε k`, and `Close-self` discharges the
-- hypothesis.
--
-- 任何常值函数在任何点、任何层级都连续
-- 模数取该层级自身的 `ε k`，假设项由 `Close-self` 消去。
const-close : (c x : RealI) (k : ℕ)
            → Σ ℚ (λ d → 0ℚ < d ×
                ((y : RealI) → Close d x y → Close (ε k) c c))
const-close c x k = ε k , (0<ε k , λ y _ → Close-self (ε k) (0<ε k) c)

------------------------------------------------------------------------
-- The zeroth partial sum is constant
--
-- 第零个部分和是常值

-- The zeroth partial sum is `0ℝ` at every point, hence continuous
-- This is the induction anchor for `expPartialℝ-close`
-- term-close has the same shape at `termℝ x n`. Its induction step needs
-- exactly one refinement, of the two moduli its two sub-calls demand — the
-- inner product's and the induction hypothesis' — because a single given
-- `Close d x x'` has to feed both; the levels of the sub-calls come from
-- `ε-archimedean` applied to the modulus of the surrounding call. The
-- reciprocal factor `recipℝ (embedℚ (embed (suc n)))` is the same term at
-- `x` and at `x'` (it depends on `n` alone), so the outer
-- `continuous-*-at` discharges its second hypothesis with `Close-self`
-- Three facts about the ℚ interface, verified while compiling this slice,
-- matter downstream: `pos*pos⇒pos` takes its instance arguments between
-- the factors (`p ⦃…⦄ q ⦃…⦄`), `positive⁻¹` takes the rational explicitly
-- and the instance hidden (`positive⁻¹ d ⦃…⦄`), and `*-monoʳ-<-pos r`
-- keeps `r` on the left (`r * p < r * q`).
--
-- 第零个部分和在每个点都是 `0ℝ`，因而连续
-- 这是 `expPartialℝ-close` 的归纳起点
-- 通项层的 `term-close` 形状相同。其归纳步只需对两次子调用所要求的两个
-- 模数做一次精化——内层乘法的与归纳假设的——因为同一个给定的
-- `Close d x x'` 要同时喂给二者；两次子调用的层级由 `ε-archimedean` 作用
-- 于外层模数得到。倒数因子 `recipℝ (embedℚ (embed (suc n)))` 在 `x` 与
-- `x'` 处是同一个项（只依赖 `n`），故外层 `continuous-*-at` 的第二个假设
-- 由 `Close-self` 消去。本片编译时核实的三条 ℚ 接口事实对后续有用：
-- `pos*pos⇒pos` 的实例参数夹在两个因子之间（`p ⦃…⦄ q ⦃…⦄`），
-- `positive⁻¹` 的第一个参数显式、实例隐式（`positive⁻¹ d ⦃…⦄`），
-- `*-monoʳ-<-pos r` 把 `r` 保持在左边（`r * p < r * q`）。
p-close-zero : (x : RealI) (k : ℕ)
             → Σ ℚ (λ d → 0ℚ < d ×
                 ((x' : RealI) → Close d x x' →
                   Close (ε k) (expPartialℝ x zero) (expPartialℝ x' zero)))
p-close-zero x k = ε k , (0<ε k , λ x' _ → Close-self (ε k) (0<ε k) 0ℝ)

------------------------------------------------------------------------
-- The term-level modulus
--
-- 通项层的模数

-- Every term of the real exponential series is continuous in its point,
-- at every level
-- Induction over `n`. At zero the term is `1ℝ` and `const-close` applies
-- At a successor the term is `(termℝ x n *ℝ x) *ℝ c` with `c` the
-- reciprocal of the embedded increment; the outer and inner
-- `continuous-*-at` calls supply the two moduli, `ε-archimedean` lowers
-- the level of each call below the next modulus, and `radius-refine`
-- produces the single radius that the outer `Close` hypothesis has to
-- supply to both.
--
-- 实数指数级数的每个通项关于其取点逐层连续
-- 关于 `n` 归纳。零处通项是 `1ℝ`，用 `const-close`。后继处通项是
-- `(termℝ x n *ℝ x) *ℝ c`，其中 `c` 是嵌入增量的倒数；外层与内层两次
-- `continuous-*-at` 给出两个模数，`ε-archimedean` 把每次调用的层级压到
-- 下一个模数之下，`radius-refine` 产出那个同时满足外层 `Close` 假设两侧
-- 要求的唯一半径。
term-close : (x : RealI) (n : ℕ) (k : ℕ)
           → Σ ℚ (λ d → 0ℚ < d ×
               ((x' : RealI) → Close d x x' →
                 Close (ε k) (termℝ x n) (termℝ x' n)))
term-close x zero k = const-close 1ℝ x k
term-close x (suc n) k =
  let
    c : RealI
    c = recipℝ (embedℚ (embed (suc n))) (0<embedℚ (embed (suc n)) (0<embed n))

    outer : Σ ℚ (λ d → 0ℚ < d ×
              ((a b : RealI) → Close d (termℝ x n *ℝ x) a → Close d c b →
                Close (ε k) ((termℝ x n *ℝ x) *ℝ c) (a *ℝ b)))
    outer = continuous-*-at (termℝ x n *ℝ x) c k

    d₀ : ℚ
    d₀ = proj₁ outer

    0<d₀ : 0ℚ < d₀
    0<d₀ = proj₁ (proj₂ outer)

    outer-step : (a b : RealI) → Close d₀ (termℝ x n *ℝ x) a → Close d₀ c b →
                 Close (ε k) ((termℝ x n *ℝ x) *ℝ c) (a *ℝ b)
    outer-step = proj₂ (proj₂ outer)

    outer-level : Σ ℕ (λ j → ε j < d₀)
    outer-level = ε-archimedean d₀ 0<d₀

    k₁ : ℕ
    k₁ = proj₁ outer-level

    εk₁<d₀ : ε k₁ < d₀
    εk₁<d₀ = proj₂ outer-level

    inner : Σ ℚ (λ d → 0ℚ < d ×
              ((a b : RealI) → Close d (termℝ x n) a → Close d x b →
                Close (ε k₁) (termℝ x n *ℝ x) (a *ℝ b)))
    inner = continuous-*-at (termℝ x n) x k₁

    d₁ : ℚ
    d₁ = proj₁ inner

    0<d₁ : 0ℚ < d₁
    0<d₁ = proj₁ (proj₂ inner)

    inner-step : (a b : RealI) → Close d₁ (termℝ x n) a → Close d₁ x b →
                 Close (ε k₁) (termℝ x n *ℝ x) (a *ℝ b)
    inner-step = proj₂ (proj₂ inner)

    ih-level : Σ ℕ (λ j → ε j < d₁)
    ih-level = ε-archimedean d₁ 0<d₁

    k₂ : ℕ
    k₂ = proj₁ ih-level

    εk₂<d₁ : ε k₂ < d₁
    εk₂<d₁ = proj₂ ih-level

    ih : Σ ℚ (λ d → 0ℚ < d ×
           ((x' : RealI) → Close d x x' →
             Close (ε k₂) (termℝ x n) (termℝ x' n)))
    ih = term-close x n k₂

    d₂ : ℚ
    d₂ = proj₁ ih

    0<d₂ : 0ℚ < d₂
    0<d₂ = proj₁ (proj₂ ih)

    ih-step : (x' : RealI) → Close d₂ x x' →
              Close (ε k₂) (termℝ x n) (termℝ x' n)
    ih-step = proj₂ (proj₂ ih)

    ref : Σ ℚ (λ d → (0ℚ < d) × ((d < d₁) × (d < d₂)))
    ref = radius-refine d₁ d₂ 0<d₁ 0<d₂

    d : ℚ
    d = proj₁ ref

    0<d : 0ℚ < d
    0<d = proj₁ (proj₂ ref)

    d<d₁ : d < d₁
    d<d₁ = proj₁ (proj₂ (proj₂ ref))

    d<d₂ : d < d₂
    d<d₂ = proj₂ (proj₂ (proj₂ ref))

    body : (x' : RealI) → Close d x x' →
           Close (ε k) (termℝ x (suc n)) (termℝ x' (suc n))
    body x' h =
      let
        x-close₁ : Close d₁ x x'
        x-close₁ = close-mono d d₁ x x' d<d₁ h

        x-close₂ : Close d₂ x x'
        x-close₂ = close-mono d d₂ x x' d<d₂ h

        t-close : Close (ε k₂) (termℝ x n) (termℝ x' n)
        t-close = ih-step x' x-close₂

        t-close₁ : Close d₁ (termℝ x n) (termℝ x' n)
        t-close₁ = close-mono (ε k₂) d₁ (termℝ x n) (termℝ x' n) εk₂<d₁ t-close

        p-close : Close (ε k₁) (termℝ x n *ℝ x) (termℝ x' n *ℝ x')
        p-close = inner-step (termℝ x' n) x' t-close₁ x-close₁

        p-close₀ : Close d₀ (termℝ x n *ℝ x) (termℝ x' n *ℝ x')
        p-close₀ = close-mono (ε k₁) d₀ (termℝ x n *ℝ x) (termℝ x' n *ℝ x')
                     εk₁<d₀ p-close

        c-close : Close d₀ c c
        c-close = Close-self d₀ 0<d₀ c
      in outer-step (termℝ x' n *ℝ x') c p-close₀ c-close
  in d , (0<d , body)

------------------------------------------------------------------------
-- The partial sums are continuous in the point
--
-- 部分和关于取点连续

-- Every partial sum of the real exponential series is continuous in its
-- point, at every level
-- Induction over `n`, exactly as for the terms: at a successor the sum is
-- `expPartialℝ x n +ℝ termℝ x n`, `continuous-+-at` supplies the outer
-- modulus, the induction hypothesis and `term-close` supply the two
-- sub-moduli, `ε-archimedean` lowers the two sub-levels, and
-- `radius-refine` merges the two sub-moduli into the single radius the
-- outer `Close` hypothesis has to supply to both.
--
-- 实数指数级数的每个部分和关于其取点逐层连续
-- 关于 `n` 归纳，与通项层同构：后继处和是
-- `expPartialℝ x n +ℝ termℝ x n`，`continuous-+-at` 给出外层模数，归纳
-- 假设与 `term-close` 给出两个子模数，`ε-archimedean` 压低两个子层级，
-- `radius-refine` 把两个子模数合成外层 `Close` 假设要同时供给两侧的唯一
-- 半径。
expPartialℝ-close : (x : RealI) (n : ℕ) (k : ℕ)
                  → Σ ℚ (λ d → 0ℚ < d ×
                      ((x' : RealI) → Close d x x' →
                        Close (ε k) (expPartialℝ x n) (expPartialℝ x' n)))
expPartialℝ-close x zero k = p-close-zero x k
expPartialℝ-close x (suc n) k =
  let
    outer : Σ ℚ (λ d → 0ℚ < d ×
              ((a b : RealI) → Close d (expPartialℝ x n) a →
                Close d (termℝ x n) b →
                Close (ε k) (expPartialℝ x n +ℝ termℝ x n) (a +ℝ b)))
    outer = continuous-+-at (expPartialℝ x n) (termℝ x n) k

    d₀ : ℚ
    d₀ = proj₁ outer

    0<d₀ : 0ℚ < d₀
    0<d₀ = proj₁ (proj₂ outer)

    outer-step : (a b : RealI) → Close d₀ (expPartialℝ x n) a →
                 Close d₀ (termℝ x n) b →
                 Close (ε k) (expPartialℝ x n +ℝ termℝ x n) (a +ℝ b)
    outer-step = proj₂ (proj₂ outer)

    outer-level : Σ ℕ (λ j → ε j < d₀)
    outer-level = ε-archimedean d₀ 0<d₀

    k₁ : ℕ
    k₁ = proj₁ outer-level

    εk₁<d₀ : ε k₁ < d₀
    εk₁<d₀ = proj₂ outer-level

    ih-sum : Σ ℚ (λ d → 0ℚ < d ×
               ((x' : RealI) → Close d x x' →
                 Close (ε k₁) (expPartialℝ x n) (expPartialℝ x' n)))
    ih-sum = expPartialℝ-close x n k₁

    d₁ : ℚ
    d₁ = proj₁ ih-sum

    0<d₁ : 0ℚ < d₁
    0<d₁ = proj₁ (proj₂ ih-sum)

    sum-step : (x' : RealI) → Close d₁ x x' →
               Close (ε k₁) (expPartialℝ x n) (expPartialℝ x' n)
    sum-step = proj₂ (proj₂ ih-sum)

    ih-term : Σ ℚ (λ d → 0ℚ < d ×
                ((x' : RealI) → Close d x x' →
                  Close (ε k₁) (termℝ x n) (termℝ x' n)))
    ih-term = term-close x n k₁

    d₂ : ℚ
    d₂ = proj₁ ih-term

    0<d₂ : 0ℚ < d₂
    0<d₂ = proj₁ (proj₂ ih-term)

    term-step : (x' : RealI) → Close d₂ x x' →
                Close (ε k₁) (termℝ x n) (termℝ x' n)
    term-step = proj₂ (proj₂ ih-term)

    ref : Σ ℚ (λ d → (0ℚ < d) × ((d < d₁) × (d < d₂)))
    ref = radius-refine d₁ d₂ 0<d₁ 0<d₂

    d : ℚ
    d = proj₁ ref

    0<d : 0ℚ < d
    0<d = proj₁ (proj₂ ref)

    d<d₁ : d < d₁
    d<d₁ = proj₁ (proj₂ (proj₂ ref))

    d<d₂ : d < d₂
    d<d₂ = proj₂ (proj₂ (proj₂ ref))

    body : (x' : RealI) → Close d x x' →
           Close (ε k) (expPartialℝ x (suc n)) (expPartialℝ x' (suc n))
    body x' h =
      let
        x-close₁ : Close d₁ x x'
        x-close₁ = close-mono d d₁ x x' d<d₁ h

        x-close₂ : Close d₂ x x'
        x-close₂ = close-mono d d₂ x x' d<d₂ h

        s-close : Close (ε k₁) (expPartialℝ x n) (expPartialℝ x' n)
        s-close = sum-step x' x-close₁

        s-close₀ : Close d₀ (expPartialℝ x n) (expPartialℝ x' n)
        s-close₀ = close-mono (ε k₁) d₀ (expPartialℝ x n) (expPartialℝ x' n)
                     εk₁<d₀ s-close

        t-close : Close (ε k₁) (termℝ x n) (termℝ x' n)
        t-close = term-step x' x-close₂

        t-close₀ : Close d₀ (termℝ x n) (termℝ x' n)
        t-close₀ = close-mono (ε k₁) d₀ (termℝ x n) (termℝ x' n) εk₁<d₀ t-close
      in outer-step (expPartialℝ x' n) (termℝ x' n) s-close₀ t-close₀
  in d , (0<d , body)

------------------------------------------------------------------------
-- A rational point strictly below a positive point
--
-- 正点下方的有理点

-- Every strictly positive point has a rational point strictly below it,
-- and that rational is positive
-- `dense` between `0ℝ` and `x` gives the point; `embedℚ-reflect` turns the
-- strict positivity at the embedded level into positivity at the rational
-- level.
--
-- 每个严格正的点下方都有一个有理点，且该有理数为正
-- 在 `0ℝ` 与 `x` 之间用 `dense` 取点；`embedℚ-reflect` 把嵌入层的严格正性
-- 翻译成有理数层的正性。
rat-below-of-pos : (x : RealI) (0<x : 0ℝ <ℝ x)
                 → Σ ℚ (λ b → (0ℚ < b) × (embedℚ b <ℝ x))
rat-below-of-pos x 0<x =
  let
    win : Σ ℚ (λ b → (0ℝ <ℝ embedℚ b) × (embedℚ b <ℝ x))
    win = dense {x = 0ℝ} {y = x} 0<x

    b : ℚ
    b = proj₁ win

    0<emb : 0ℝ <ℝ embedℚ b
    0<emb = proj₁ (proj₂ win)

    emb<x : embedℚ b <ℝ x
    emb<x = proj₂ (proj₂ win)

    0<b : 0ℚ < b
    0<b = embedℚ-reflect 0ℚ b 0<emb
  in b , (0<b , emb<x)

------------------------------------------------------------------------
-- An ε below a positive point
--
-- 正点下方的 ε

-- Every strictly positive point has some `ε k` strictly below it
-- The rational point below `x` supplies a positive rational `b`;
-- `ε-archimedean` at `b` lowers the level, `embedℚ-mono` lifts the
-- rational comparison to the reals, and transitivity closes it.
--
-- 每个严格正的点下方都有某个 `ε k`
-- `x` 下方的有理点给出正有理数 `b`；对 `b` 用 `ε-archimedean` 压低层级，
-- `embedℚ-mono` 把有理比较抬到实数层，传递性收尾。
ε-below-real : (z : RealI) (0<z : 0ℝ <ℝ z)
             → Σ ℕ (λ k → embedℚ (ε k) <ℝ z)
ε-below-real z 0<z =
  let
    below : Σ ℚ (λ b → (0ℚ < b) × (embedℚ b <ℝ z))
    below = rat-below-of-pos z 0<z

    b : ℚ
    b = proj₁ below

    0<b : 0ℚ < b
    0<b = proj₁ (proj₂ below)

    emb<z : embedℚ b <ℝ z
    emb<z = proj₂ (proj₂ below)

    ar : Σ ℕ (λ k → ε k < b)
    ar = ε-archimedean b 0<b

    k : ℕ
    k = proj₁ ar

    εk<b : ε k < b
    εk<b = proj₂ ar

    emb-εk<emb-b : embedℚ (ε k) <ℝ embedℚ b
    emb-εk<emb-b = embedℚ-mono (ε k) b εk<b
  in k , <-transR emb-εk<emb-b emb<z

------------------------------------------------------------------------
-- Real bridges for the radius
--
-- 半径步骤的实数桥

-- Shrinking by a positive rational stays strictly below the point
-- This is the embedded instance of the general law `sub-pos-lt`.
--
-- 减去正有理数后仍严格低于该点
-- 这是通用律 `sub-pos-lt` 的嵌入实例。
sub-emb-lt : (x : RealI) (e : ℚ) → 0ℚ < e → x -ℝ embedℚ e <ℝ x
sub-emb-lt x e 0<e = sub-pos-lt x (embedℚ e) (0<embedℚ e 0<e)

-- A point strictly above an embedded rational is strictly positive after
-- subtracting that rational
-- Add `negℝ (embedℚ e)` to both sides of `embedℚ e <ℝ x`; the left side
-- collapses to `0ℝ` by `+ℝ-inverseʳ`.
--
-- 高于嵌入有理数的点，减去该有理数后严格为正
-- 在 `embedℚ e <ℝ x` 两侧加 `negℝ (embedℚ e)`，左侧由 `+ℝ-inverseʳ`
-- 收缩为 `0ℝ`。
sub-emb-pos : (x : RealI) (e : ℚ) → embedℚ e <ℝ x → 0ℝ <ℝ x -ℝ embedℚ e
sub-emb-pos x e emb<x =
  ≈-<-resp (+ℝ-inverseʳ (embedℚ e))
    (<-+mono (embedℚ e) x (negℝ (embedℚ e)) emb<x)

------------------------------------------------------------------------
-- Replacing the point by a rational point below it
--
-- 换到下方的有理点

-- The one-way corollary: if `r` is strictly below the partial sum at the
-- strictly positive point `x`, then some non-negative rational point `q`
-- below `x` still has `r` strictly below its partial sum
-- The gap turns into an `ε k` budget first: `dense` picks a rational `b`
-- between `r` and the partial sum, `ε-archimedean` puts `ε k` below
-- `b - r`, and `shift-below` concludes `r + ε k < b`. Continuity at
-- level `k` gives a radius `d`; it is shrunk below both `d` and a rational
-- point `b₂` under `x`, and `dense` between `x - d'` and `x` supplies the
-- point `q`. Since `q` is within `d'` of `x`, `close-left` bounds
-- `expPartialℝ x n - expPartialℝ q n` by `embedℚ (ε k)`; the two bounds
-- `r + ε k < expPartialℝ x n` and `expPartialℝ x n < expPartialℝ q n + ε k`
-- cancel `ε k` on the right and yield `r < expPartialℝ q n`
-- The shrinking below `b₂` is what makes `q` non-negative: `x - d'` stays
-- above `0ℝ`, so the point picked between `x - d'` and `x` is positive, and
-- `embedℚ-reflect` lowers that to `0ℚ < q`.
--
-- 单向推论：若 `r` 严格低于严格正点 `x` 处的部分和，则存在不超过 `x` 的
-- 非负有有理点 `q`，其部分和仍严格高于 `r`
-- 先把间隙换成 `ε k` 的预算：`dense` 在 `r` 与部分和之间取有理点 `b`，
-- `ε-archimedean` 把 `ε k` 放到 `b - r` 之下，`shift-below` 收成
-- `r + ε k < b`。层级 `k` 处的连续性给出半径 `d`；把 `d` 压到既小于 `d`
-- 又小于 `x` 下方某个有理点 `b₂`，再用 `dense` 在 `x - d'` 与 `x` 之间取
-- 点 `q`。因 `q` 与 `x` 相距 `d'` 以内，`close-left` 把
-- `expPartialℝ x n - expPartialℝ q n` 界在 `embedℚ (ε k)` 之下；两个界
-- `r + ε k < expPartialℝ x n` 与 `expPartialℝ x n < expPartialℝ q n + ε k`
-- 在右侧消去 `ε k`，得 `r < expPartialℝ q n`
-- 把半径压到 `b₂` 之下正是 `q` 非负的来源：`x - d'` 仍在 `0ℝ` 之上，故取在
-- `x - d'` 与 `x` 之间的点为正，`embedℚ-reflect` 再把它降到 `0ℚ < q`。
expPartialℝ-below-rat : (x : RealI) (0<x : 0ℝ <ℝ x) (n : ℕ) (r : ℚ)
                      (r<p : embedℚ r <ℝ expPartialℝ x n) →
                      Σ ℚ (λ q → (0ℚ ≤ q) × (embedℚ q <ℝ x) ×
                                 (embedℚ r <ℝ expPartialℝ (embedℚ q) n))
expPartialℝ-below-rat x 0<x n r r<p =
  let
    win : Σ ℚ (λ b → (embedℚ r <ℝ embedℚ b) × (embedℚ b <ℝ expPartialℝ x n))
    win = dense {x = embedℚ r} {y = expPartialℝ x n} r<p

    b : ℚ
    b = proj₁ win

    emb-r<emb-b : embedℚ r <ℝ embedℚ b
    emb-r<emb-b = proj₁ (proj₂ win)

    emb-b<P : embedℚ b <ℝ expPartialℝ x n
    emb-b<P = proj₂ (proj₂ win)

    r<b : r < b
    r<b = embedℚ-reflect r b emb-r<emb-b

    0<b-r : 0ℚ < b - r
    0<b-r = pos-diff r b r<b

    ar : Σ ℕ (λ j → ε j < b - r)
    ar = ε-archimedean (b - r) 0<b-r

    k : ℕ
    k = proj₁ ar

    εk<b-r : ε k < b - r
    εk<b-r = proj₂ ar

    shift-below : (e : ℚ) → e < b - r → r + e < b
    shift-below e e< =
      subst (λ w → r + e < w) (sub-add-cancel b r)
        (subst (λ w → w < (b - r) + r) (+-comm e r) (+-monoˡ-< r e<))

    r+εk<b : r + ε k < b
    r+εk<b = shift-below (ε k) εk<b-r

    emb-r+εk<P : embedℚ (r + ε k) <ℝ expPartialℝ x n
    emb-r+εk<P = <-transR (embedℚ-mono (r + ε k) b r+εk<b) emb-b<P

    sum-close : embedℚ r +ℝ embedℚ (ε k) <ℝ expPartialℝ x n
    sum-close = ≈-<-resp (embedℚ-+ r (ε k)) emb-r+εk<P

    mod : Σ ℚ (λ d → (0ℚ < d) ×
            ((x' : RealI) → Close d x x' →
              Close (ε k) (expPartialℝ x n) (expPartialℝ x' n)))
    mod = expPartialℝ-close x n k

    d : ℚ
    d = proj₁ mod

    0<d : 0ℚ < d
    0<d = proj₁ (proj₂ mod)

    cont : (x' : RealI) → Close d x x' →
           Close (ε k) (expPartialℝ x n) (expPartialℝ x' n)
    cont = proj₂ (proj₂ mod)

    below : Σ ℚ (λ c → (0ℚ < c) × (embedℚ c <ℝ x))
    below = rat-below-of-pos x 0<x

    b₂ : ℚ
    b₂ = proj₁ below

    0<b₂ : 0ℚ < b₂
    0<b₂ = proj₁ (proj₂ below)

    emb-b₂<x : embedℚ b₂ <ℝ x
    emb-b₂<x = proj₂ (proj₂ below)

    ref : Σ ℚ (λ dd → (0ℚ < dd) × ((dd < d) × (dd < b₂)))
    ref = radius-refine d b₂ 0<d 0<b₂

    d' : ℚ
    d' = proj₁ ref

    0<d' : 0ℚ < d'
    0<d' = proj₁ (proj₂ ref)

    d'<d : d' < d
    d'<d = proj₁ (proj₂ (proj₂ ref))

    d'<b₂ : d' < b₂
    d'<b₂ = proj₂ (proj₂ (proj₂ ref))

    emb-d'<x : embedℚ d' <ℝ x
    emb-d'<x = <-transR (embedℚ-mono d' b₂ d'<b₂) emb-b₂<x

    0<x-d' : 0ℝ <ℝ x -ℝ embedℚ d'
    0<x-d' = sub-emb-pos x d' emb-d'<x

    x-d'<x : x -ℝ embedℚ d' <ℝ x
    x-d'<x = sub-emb-lt x d' 0<d'

    pick : Σ ℚ (λ q → ((x -ℝ embedℚ d') <ℝ embedℚ q) × (embedℚ q <ℝ x))
    pick = dense {x = x -ℝ embedℚ d'} {y = x} x-d'<x

    q : ℚ
    q = proj₁ pick

    lo<emb-q : (x -ℝ embedℚ d') <ℝ embedℚ q
    lo<emb-q = proj₁ (proj₂ pick)

    emb-q<x : embedℚ q <ℝ x
    emb-q<x = proj₂ (proj₂ pick)

    0<emb-q : 0ℝ <ℝ embedℚ q
    0<emb-q = <-transR 0<x-d' lo<emb-q

    0<q : 0ℚ < q
    0<q = embedℚ-reflect 0ℚ q 0<emb-q

    0≤q : 0ℚ ≤ q
    0≤q = <⇒≤ 0<q

    x<x+d' : x <ℝ x +ℝ embedℚ d'
    x<x+d' = ≈-<-respʳ (+ℝ-comm (embedℚ d') x)
               (≈-<-resp (+ℝ-identityˡ x)
                 (<-+mono 0ℝ (embedℚ d') x (0<embedℚ d' 0<d')))

    emb-q<x+d' : embedℚ q <ℝ x +ℝ embedℚ d'
    emb-q<x+d' = <-transR emb-q<x x<x+d'

    q-closed : Close d' x (embedℚ q)
    q-closed = lo<emb-q , emb-q<x+d'

    q-close : Close d x (embedℚ q)
    q-close = close-mono d' d x (embedℚ q) d'<d q-closed

    gap : expPartialℝ x n -ℝ expPartialℝ (embedℚ q) n <ℝ embedℚ (ε k)
    gap = close-left (ε k) (expPartialℝ x n) (expPartialℝ (embedℚ q) n)
            (cont (embedℚ q) q-close)

    P : RealI
    P = expPartialℝ x n

    A : RealI
    A = expPartialℝ (embedℚ q) n

    P<A+E : P <ℝ A +ℝ embedℚ (ε k)
    P<A+E = ≈-<-respʳ (+ℝ-comm (embedℚ (ε k)) A)
              (≈-<-resp (sub-add-cancelℝ P A)
                (<-+mono (P -ℝ A) (embedℚ (ε k)) A gap))

    final : embedℚ r <ℝ A
    final = <-+mono-reflect {x = A} {y = embedℚ r} {z = embedℚ (ε k)}
              (<-transR sum-close P<A+E)
  in q , (0≤q , (emb-q<x , final))

------------------------------------------------------------------------
-- Rational points of a prescribed width around a real
--
-- 实数附近给定宽度的有理点

-- Both pickers are `dense` applied to a shifted endpoint. They are the
-- two halves of the rational window consumed by the closed-window
-- squeeze of the exponential: an upper point within `w`, and a lower
-- point within `w`.
--
-- 两个取点器都是把 `dense` 用在平移后的端点上。它们正是指数窗户夹逼
-- 所需的那个有理窗的两半：上方不超过 `w` 的点，与下方不超过 `w` 的点。
rat-above : (x : RealI) (w : ℚ) (0<w : 0ℚ < w)
          → Σ ℚ (λ q → x <ℝ embedℚ q × embedℚ q <ℝ x +ℝ embedℚ w)
rat-above x w 0<w =
  let
    x<x+w : x <ℝ x +ℝ embedℚ w
    x<x+w = ≈-<-respʳ (+ℝ-comm (embedℚ w) x)
              (≈-<-resp (+ℝ-identityˡ x)
                (<-+mono 0ℝ (embedℚ w) x (0<embedℚ w 0<w)))
  in
    dense {x} {x +ℝ embedℚ w} x<x+w

rat-below : (x : RealI) (w : ℚ) (0<w : 0ℚ < w)
          → Σ ℚ (λ p → x -ℝ embedℚ w <ℝ embedℚ p × embedℚ p <ℝ x)
rat-below x w 0<w =
  let
    p<p+w : x -ℝ embedℚ w <ℝ (x -ℝ embedℚ w) +ℝ embedℚ w
    p<p+w = ≈-<-respʳ (+ℝ-comm (embedℚ w) (x -ℝ embedℚ w))
              (≈-<-resp (+ℝ-identityˡ (x -ℝ embedℚ w))
                (<-+mono 0ℝ (embedℚ w) (x -ℝ embedℚ w) (0<embedℚ w 0<w)))

    p<x : x -ℝ embedℚ w <ℝ x
    p<x = ≈-<-respʳ (sub-add-cancelℝ x (embedℚ w)) p<p+w
  in
    dense {x -ℝ embedℚ w} {x} p<x

------------------------------------------------------------------------
-- A rational window of prescribed width containing a real
--
-- 包含给定实数的定宽有理窗

-- Take a rational point `p` below `x` but within `w` of it, so that
-- `x - w < embed p < x`. Adding `w` on both sides turns the lower bound
-- into `embed p + embed w > x`, and the embedding of `p + w` is the sum
-- of the two embeddings, so the window `[p, p + w]` contains `x` with
-- width exactly `w`.
--
-- 先在 `x` 下方 `w` 之内取有理点 `p`，使 `x - w < embed p < x`。两边加
-- `w` 把下界变成 `embed p + embed w > x`，而 `p + w` 的嵌入正是两个嵌入
-- 之和，故窗 `[p, p + w]` 含 `x`，宽恰为 `w`。
rat-window : (x : RealI) (w : ℚ) (0<w : 0ℚ < w)
           → Σ ℚ (λ p → (x -ℝ embedℚ w <ℝ embedℚ p)
                        × (embedℚ p <ℝ x × x <ℝ embedℚ (p + w)))
rat-window x w 0<w =
  let
    down : Σ ℚ (λ p → x -ℝ embedℚ w <ℝ embedℚ p × embedℚ p <ℝ x)
    down = rat-below x w 0<w

    p : ℚ
    p = proj₁ down

    x-w<p : x -ℝ embedℚ w <ℝ embedℚ p
    x-w<p = proj₁ (proj₂ down)

    p<x : embedℚ p <ℝ x
    p<x = proj₂ (proj₂ down)

    shift : (x -ℝ embedℚ w) +ℝ embedℚ w <ℝ embedℚ p +ℝ embedℚ w
    shift = <-+mono (x -ℝ embedℚ w) (embedℚ p) (embedℚ w) x-w<p

    x<p+w : x <ℝ embedℚ p +ℝ embedℚ w
    x<p+w = ≈-<-resp (sub-add-cancelℝ x (embedℚ w)) shift

    emb-p+w≈ : embedℚ p +ℝ embedℚ w ≈ℝ embedℚ (p + w)
    emb-p+w≈ = ≈ℝ-sym (embedℚ-+ p w)

    x<p+w' : x <ℝ embedℚ (p + w)
    x<p+w' = ≈-<-respʳ emb-p+w≈ x<p+w
  in
    p , (x-w<p , (p<x , x<p+w'))

------------------------------------------------------------------------
-- A rational window of prescribed width below a real point
--
-- 位于实数点下方、给定宽度的有理窗

-- When the width stays below the point itself, the window is pushed to
-- the right of `0`, so its lower endpoint is a nonnegative rational:
-- `x - w > 0` and `x - w < embed p` put `embed p` above zero, and
-- `embedℚ-reflect` lowers that to a rational comparison.
--
-- 当窗宽小于该点本身时，窗被推到 `0` 的右侧，故其下端点是非负有理数：
-- `x - w > 0` 与 `x - w < embed p` 把 `embed p` 抬到零以上，
-- `embedℚ-reflect` 再把它降到有理层的比较。
rat-window-pos : (x : RealI) (w : ℚ) (0<w : 0ℚ < w) (w<x : embedℚ w <ℝ x)
               → Σ ℚ (λ p → (0ℚ ≤ p) × (embedℚ p <ℝ x × x <ℝ embedℚ (p + w)))
rat-window-pos x w 0<w w<x =
  let
    win : Σ ℚ (λ p → (x -ℝ embedℚ w <ℝ embedℚ p)
                          × (embedℚ p <ℝ x × x <ℝ embedℚ (p + w)))
    win = rat-window x w 0<w

    p : ℚ
    p = proj₁ win

    x-w<p : x -ℝ embedℚ w <ℝ embedℚ p
    x-w<p = proj₁ (proj₂ win)

    p<x : embedℚ p <ℝ x
    p<x = proj₁ (proj₂ (proj₂ win))

    x<p+w : x <ℝ embedℚ (p + w)
    x<p+w = proj₂ (proj₂ (proj₂ win))

    0<x-w : 0ℝ <ℝ x -ℝ embedℚ w
    0<x-w = sub-emb-pos x w w<x

    0<emb-p : 0ℝ <ℝ embedℚ p
    0<emb-p = <-transR 0<x-w x-w<p

    0<p : 0ℚ < p
    0<p = embedℚ-reflect 0ℚ p 0<emb-p
  in
    p , (<⇒≤ 0<p , (p<x , x<p+w))
