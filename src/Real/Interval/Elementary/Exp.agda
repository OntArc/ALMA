------------------------------------------------------------------------
-- The real exponential as a cut
--
-- 实指数：定义所用的割
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Elementary.Exp where

open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_≤_ to _≤ℕ_; _+_ to _+ℕ_)
open import Data.Nat.Properties as ℕP using (+-comm; m∸n+n≡m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; 1/_; _+_; _-_; _*_; _≤_; _<_)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; <⇒≤; ≤-<-trans; <-≤-trans; ≮⇒≥; +-identityˡ; +-identityʳ
  ; +-assoc; +-monoʳ-<; +-mono-≤; +-mono-<-≤; ≤-reflexive; <-cmp
  ; *-distribˡ-+; *-comm; *-identityˡ; *-identityʳ; pos⇒nonZero)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; subst)

open import Base.RationalRing using (0<1)
open import Real using (embed; embed-mono-≤; 0<embed; embed-suc-pos)
open import Real.IntervalEquiv using (l; u; width; node; u-mono0)
open import Real.Interval as R using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ)
open import Real.Interval.Continuity using (embedℚ-mono)
open import Real.Interval.DensityArch using (dense; archimedean)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym)
open import Real.Interval.Exp.Dense using (lt-split)
open import Real.Interval.Exp.Core using
  (expPartial; expPartial-zero; expPartial-nonNeg; expPartial-le; exp-bracket-le)
open import Real.Interval.Exp.Order using (expPartial-le-param)
open import Real.Interval.Exp.Lipschitz using
  (expPartial-param-bnd; expPartial-bound)
open import Real.Interval.Exp.Series using
  (termℝ; termℝ-nonNeg; expPartialℝ; expPartialℝ-nonNeg; expPartialℝ-≤-of-bound
  ; expPartialℝ-≥-of-bound)
open import Real.Interval.Kit using (*-mono-≤-nonNeg)
open import Real.Interval.Node using (add2-nonNeg)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Base using
  (Subset; Occupied; Upper; Located; _≤ℝ_; ≤ℝ-trans)
open import Real.Interval.OrderLe using
  (<⇒≤ℝ; ≈⇒≤ℝ; ≤ℝ-<trans; <-≤ℝ-trans; ≤ℝ-refl)
open import Real.Interval.OrderComplete using (sup; sup-upper; sup-least)
open import Real.Interval.OrderLaws using (≈-<-resp; width-below-strict)
open import Real.Interval.Rational using
  (pos-diff; plus-diff; ÷-cancel; ÷-pos; *-<-mono-right; recip-add-lt-one)
open import Real.Interval.Series.Core using (sum-mono-tail)
open import Real.Interval.Series.Bounds using (le-self-add)
open import Real.Interval.Sqrt.Bounds using
  (embedℚ-≤; embedℚ-reflect; l-layer-≤; u-layer-≤)

------------------------------------------------------------------------
-- The subset
--
-- 子集

-- A real r is in P when it is a rational q and some partial sum of the
-- series at x reaches q.
--
-- 实数 r 属于 P，当它是某个有理数 q，且 x 处级数的某个部分和达到 q。
module _ (x : RealI) (0≤x : 0ℝ ≤ℝ x) where

  Pℝ : Subset
  Pℝ r = Σ ℚ (λ q → (r ≈ℝ embedℚ q) × Σ ℕ (λ n → embedℚ q ≤ℝ expPartialℝ x n))

  Pℝ-member : (q : ℚ)
            → Σ ℕ (λ n → embedℚ q ≤ℝ expPartialℝ x n)
            → Pℝ (embedℚ q)
  Pℝ-member q w = q , (≈ℝ-refl , w)

  ----------------------------------------------------------------------
  -- Partial sums increase with the index
  --
  -- 部分和随下标递增

  -- The index gap: m is n plus the difference when n ≤ m.
  --
  -- 下标差：n ≤ m 时，m 等于 n 加上差值。
  gap : (n m : ℕ) → n ≤ℕ m → n +ℕ (m ∸ n) ≡ m
  gap n m n≤m = trans (+-comm n (m ∸ n)) (m∸n+n≡m {m = m} {n = n} n≤m)

  expPartialℝ-mono-n : (n m : ℕ) → n ≤ℕ m
                     → expPartialℝ x n ≤ℝ expPartialℝ x m
  expPartialℝ-mono-n n m n≤m =
    subst (λ k → expPartialℝ x n ≤ℝ expPartialℝ x k)
          (gap n m n≤m)
          (sum-mono-tail (termℝ x) (termℝ-nonNeg x 0≤x) n (m ∸ n))

  ----------------------------------------------------------------------
  -- Membership is inherited by larger indices
  --
  -- 成员资格沿更大的下标继承

  Pℝ-mono-n : (q : ℚ) (n m : ℕ) → n ≤ℕ m
            → embedℚ q ≤ℝ expPartialℝ x n
            → Σ ℕ (λ j → embedℚ q ≤ℝ expPartialℝ x j)
  Pℝ-mono-n q n m n≤m q≤n =
    m , ≤ℝ-trans {x = embedℚ q} {y = expPartialℝ x n}
                 {z = expPartialℝ x m} q≤n (expPartialℝ-mono-n n m n≤m)

  ----------------------------------------------------------------------
  -- A point strictly below a partial sum occupies the lower bracket
  --
  -- 严格低于部分和的点占据下括号

  -- Density gives a rational between p and the partial sum; it is a
  -- member because it lies below that partial sum, and it lies strictly
  -- above p.
  --
  -- 稠密性给出 p 与部分和之间的有理数；它低于该部分和故为成员，且严格高于 p。
  Pℝ-occupied-of-strict : (p : ℚ) (n : ℕ)
                        → embedℚ p <ℝ expPartialℝ x n
                        → Occupied Pℝ p
  Pℝ-occupied-of-strict p n p<sn =
    let d : Σ ℚ (λ q → (embedℚ p <ℝ embedℚ q) × (embedℚ q <ℝ expPartialℝ x n))
        d = dense {x = embedℚ p} {y = expPartialℝ x n} p<sn
        q = proj₁ d
        p<q = proj₁ (proj₂ d)
        q<s = proj₂ (proj₂ d)
        q≤s : embedℚ q ≤ℝ expPartialℝ x n
        q≤s = <⇒≤ℝ q<s
    in
      embedℚ q , (Pℝ-member q (n , q≤s) , p<q)

  ----------------------------------------------------------------------
  -- A uniform rational window for the real partial sums
  --
  -- 实数部分和的一致有理窗口

  -- If m ≤ x ≤ m + h and every rational partial sum at m + h stays below
  -- B, then at every index the real partial sum at x lies between the
  -- rational partial sum at m and that same sum shifted by h·(1+B). The
  -- width of the window does not depend on the index.
  --
  -- 若 m ≤ x ≤ m + h，且 m + h 处的有理部分和一概不超过 B，则任意下标处
  -- 实数部分和都夹在 m 处有理部分和与它平移 h·(1+B) 之间。窗口宽度与下标
  -- 无关。
  expPartialℝ-window :
      (m h B : ℚ) (0≤m : 0ℚ ≤ m) (0≤h : 0ℚ ≤ h)
    → embedℚ m ≤ℝ x → x ≤ℝ embedℚ (m + h)
    → (∀ j → expPartial (m + h) j ≤ B)
    → (n : ℕ)
    → (embedℚ (expPartial m n) ≤ℝ expPartialℝ x n)
      × (expPartialℝ x n ≤ℝ embedℚ (expPartial m n + h * (1ℚ + B)))
  expPartialℝ-window m h B 0≤m 0≤h m≤x x≤mh bnd n =
    let
      0≤mh : 0ℚ ≤ m + h
      0≤mh = add2-nonNeg 0≤m 0≤h

      step : expPartial (m + h) n ≤ expPartial m n + h * (1ℚ + B)
      step = expPartial-param-bnd m h 0≤m 0≤h n B bnd

      upper : expPartialℝ x n ≤ℝ embedℚ (expPartial m n + h * (1ℚ + B))
      upper = ≤ℝ-trans (expPartialℝ-≤-of-bound x (m + h) 0≤x x≤mh 0≤mh n)
                       (embedℚ-≤ (expPartial (m + h) n)
                                 (expPartial m n + h * (1ℚ + B)) step)
    in
      expPartialℝ-≥-of-bound x m 0≤m m≤x n , upper

  ----------------------------------------------------------------------
  -- A bracket around x whose lower end is non-negative
  --
  -- 下端点非负的 x 括号

  -- The lower layer endpoint may be negative; the Lipschitz estimate
  -- needs a non-negative lower end, so in that case the bracket is taken
  -- from zero up to the upper layer endpoint. The width then only
  -- shrinks: the upper endpoint is below the layer width whenever the
  -- lower endpoint is below zero. The last component records that the
  -- bracket top never exceeds the layer-zero upper endpoint, which is
  -- what carries the global bound B0 down to the window.
  --
  -- 下层端点可能为负，而 Lipschitz 估计要求下端点非负；此时括号取从零到
  -- 上层端点。宽度只会更小：下端点低于零时，上层端点低于该层宽度。末项
  -- 记录括号上端不超过第零层上端点，整体界 B₀ 正是靠它带到窗口上。
  BracketData : (k : ℕ) → Set
  BracketData k =
    Σ ℚ (λ m → Σ ℚ (λ h →
      (0ℚ ≤ m) × (0ℚ ≤ h) × (embedℚ m ≤ℝ x) × (x ≤ℝ embedℚ (m + h))
      × (h ≤ width x k) × (m + h ≤ u x zero)))

  bracket-zero : (k : ℕ) → l x k ≤ 0ℚ → BracketData k
  bracket-zero k l≤0 =
    let
      uk : ℚ
      uk = u x k

      wk : ℚ
      wk = width x k

      eu : 0ℝ ≤ℝ embedℚ uk
      eu = ≤ℝ-trans 0≤x (u-layer-≤ x k)

      0≤u : 0ℚ ≤ uk
      0≤u = ≮⇒≥ (λ uk<0 → eu (embedℚ-mono uk 0ℚ uk<0))

      x≤0u : x ≤ℝ embedℚ (0ℚ + uk)
      x≤0u = subst (λ z → x ≤ℝ embedℚ z) (sym (+-identityˡ uk))
                  (u-layer-≤ x k)

      -- The upper endpoint is below the layer width when the lower one is
      -- at most zero: u = l + width ≤ 0 + width = width.
      --
      -- 下端点不超过零时，上端点低于该层宽度：u = l + width ≤ 0 + width = width。
      lw≤w : l x k + wk ≤ wk
      lw≤w = ≤-trans (+-mono-≤ l≤0 (≤-refl {wk}))
                     (≤-reflexive (+-identityˡ wk))

      u≤w : uk ≤ wk
      u≤w = subst (λ z → z ≤ wk) (plus-diff (l x k) uk) lw≤w

      -- The window sits below the layer-zero upper endpoint, so the
      -- global bound B₀ applies to it.
      --
      -- 窗口落在第零层上端点之下，故整体界 B₀ 适用于它。
      mh≤U₀ : 0ℚ + uk ≤ u x zero
      mh≤U₀ = subst (λ z → z ≤ u x zero) (sym (+-identityˡ uk)) (u-mono0 x k)
    in
      0ℚ , uk , (≤-refl , (0≤u , (0≤x , (x≤0u , (u≤w , mh≤U₀)))))

  bracket-positive : (k : ℕ) → Tri (0ℚ < l x k) (0ℚ ≡ l x k) (l x k < 0ℚ)
                   → BracketData k
  bracket-positive k (tri< 0<l _ _) =
    let
      0≤l : 0ℚ ≤ l x k
      0≤l = <⇒≤ 0<l

      0≤w : 0ℚ ≤ width x k
      0≤w = <⇒≤ (pos-diff (l x k) (u x k) (R.RealI.lo (node x k)))

      l+w≡u : l x k + width x k ≡ u x k
      l+w≡u = plus-diff (l x k) (u x k)

      x≤lw : x ≤ℝ embedℚ (l x k + width x k)
      x≤lw = subst (λ z → x ≤ℝ embedℚ z) (sym l+w≡u) (u-layer-≤ x k)

      mh≤U₀ : l x k + width x k ≤ u x zero
      mh≤U₀ = subst (λ z → z ≤ u x zero) (sym l+w≡u) (u-mono0 x k)
    in
      l x k , width x k , (0≤l , (0≤w , (l-layer-≤ x k , (x≤lw , (≤-refl , mh≤U₀)))))

  bracket-positive k (tri≈ _ e _) = bracket-zero k (≤-reflexive (sym e))
  bracket-positive k (tri> _ _ l<0) = bracket-zero k (<⇒≤ l<0)

  bracketAt : (k : ℕ) → BracketData k
  bracketAt k = bracket-positive k (<-cmp 0ℚ (l x k))

  ----------------------------------------------------------------------
  -- A rational upper bound
  --
  -- 有理上界

  -- The layer-zero upper endpoint U₀ bounds x from above and is
  -- non-negative. The rational partial sums at U₀ have a global bound B₀,
  -- and argument monotonicity carries it down to every m + h ≤ U₀ used in
  -- the window. The strict upper bound for the subset is B₀ + 1.
  --
  -- 第零层的上端点 U₀ 从上方界住 x 且非负。U₀ 处的有理部分和有整体界 B₀，
  -- 参数单调性把它带到窗口中用到的一切 m + h ≤ U₀。子集所需的严格上界
  -- 取 B₀ + 1。
  U₀ : ℚ
  U₀ = u x zero

  x≤U₀ : x ≤ℝ embedℚ U₀
  x≤U₀ = u-layer-≤ x zero

  0≤U₀ : 0ℚ ≤ U₀
  0≤U₀ = ≮⇒≥ (λ U<0 → ≤ℝ-trans 0≤x x≤U₀ (embedℚ-mono U₀ 0ℚ U<0))

  bound₀ : Σ ℚ (λ B → ∀ j → expPartial U₀ j ≤ B)
  bound₀ = expPartial-bound U₀ 0≤U₀ 1ℚ 0<1

  B₀ : ℚ
  B₀ = proj₁ bound₀

  bnd₀ : ∀ j → expPartial U₀ j ≤ B₀
  bnd₀ = proj₂ bound₀

  -- Positivity of the bound, and of the shift by one. The width control
  -- for locatedness needs `1+B₀ > 0` as the denominator of the shrinking
  -- target, and `B₀ ≥ 0` to keep products monotone.
  --
  -- 界为正，平移一之后也为正。定位性的宽度控制要把 1+B₀ 当缩小目标的分母，
  -- 也需要 B₀ ≥ 0 来保证乘积单调。
  0≤B₀ : 0ℚ ≤ B₀
  0≤B₀ = subst (λ z → z ≤ B₀) (expPartial-zero U₀) (bnd₀ zero)

  0<1+B₀ : 0ℚ < 1ℚ + B₀
  0<1+B₀ = subst (λ z → z < 1ℚ + B₀) (+-identityˡ 0ℚ) (+-mono-<-≤ 0<1 0≤B₀)

  B₀<B₀+1 : B₀ < B₀ + 1ℚ
  B₀<B₀+1 = subst (λ z → z < B₀ + 1ℚ) (+-identityʳ B₀) (+-monoʳ-< B₀ 0<1)

  Pℝ-upper : (r : RealI) → Pℝ r → r <ℝ embedℚ (B₀ + 1ℚ)
  Pℝ-upper r (q , (r≈ , n , q≤n)) =
    let
      q≤p : embedℚ q ≤ℝ expPartialℝ x n
      q≤p = q≤n

      p≤eB : expPartialℝ x n ≤ℝ embedℚ (expPartial U₀ n)
      p≤eB = expPartialℝ-≤-of-bound x U₀ 0≤x x≤U₀ 0≤U₀ n

      eB≤eB₀ : embedℚ (expPartial U₀ n) ≤ℝ embedℚ B₀
      eB≤eB₀ = embedℚ-≤ (expPartial U₀ n) B₀ (bnd₀ n)

      eq≤eB₀ : embedℚ q ≤ℝ embedℚ B₀
      eq≤eB₀ = ≤ℝ-trans q≤p (≤ℝ-trans p≤eB eB≤eB₀)

      q≤B₀ : q ≤ B₀
      q≤B₀ = ≮⇒≥ (λ B<q → eq≤eB₀ (embedℚ-mono B₀ q B<q))

      q<B₀+1 : q < B₀ + 1ℚ
      q<B₀+1 = ≤-<-trans q≤B₀ B₀<B₀+1

      strict : embedℚ q <ℝ embedℚ (B₀ + 1ℚ)
      strict = embedℚ-mono q (B₀ + 1ℚ) q<B₀+1
    in
      ≈-<-resp (≈ℝ-sym r≈) strict

  ----------------------------------------------------------------------
  -- The subset is bounded above, in the form `sup` consumes
  --
  -- 子集有上界，且取 `sup` 所需的形式

  -- The cut's upper-bound argument needs the non-strict form.
  --
  -- 割的上界论证要的是非严格形式。
  Pℝ-isUpper : (r : RealI) → Pℝ r → r ≤ℝ embedℚ (B₀ + 1ℚ)
  Pℝ-isUpper r pr = <⇒≤ℝ (Pℝ-upper r pr)
  ----------------------------------------------------------------------
  -- Locatedness
  --
  -- 定位性

  -- A trichotomy on p against expPartial m N decides the case. Strictly
  -- below means a member lies above p; otherwise the tail tolerance d
  -- plus the window shift W keeps every member below q.
  --
  -- 对 p 与 expPartial m N 做三分类即定：前者严格小则有成员在 p 之上；
  -- 否则尾部容差 d 加窗口位移 W 把每个成员都压在 q 之下。
  expPartial-mN : (m : ℚ) (0≤m : 0ℚ ≤ m) (N : ℕ) (d : ℚ) (0≤d : 0ℚ ≤ d)
                → ((j : ℕ) → N ≤ℕ j → expPartial m j ≤ expPartial m N + d)
                → (n : ℕ) → expPartial m n ≤ expPartial m N + d
  expPartial-mN m 0≤m N d 0≤d tail n =
    [ (λ n≤N → ≤-trans (expPartial-le m 0≤m n N n≤N)
                       (le-self-add {p = expPartial m N} {q = d} 0≤d))
    , (λ N≤n → tail n N≤n) ]′ (ℕP.≤-total n N)

  located-aux : (p q : ℚ) (k : ℕ) (d : ℚ) (0<d : 0ℚ < d)
              → ((hh : ℚ) → 0ℚ ≤ hh → hh ≤ width x k → hh * (1ℚ + B₀) < d)
              → d + d < q - p
              → BracketData k → Occupied Pℝ p ⊎ Upper Pℝ q
  located-aux p q k d 0<d W<dAt d+d<A
      (m , h , 0≤m , 0≤h , m≤x , x≤mh , h≤w , mh≤U₀) =
    let
      C : ℚ
      C = 1ℚ + B₀

      W : ℚ
      W = h * C

      W<d : W < d
      W<d = W<dAt h 0≤h h≤w

      0≤mh : 0ℚ ≤ m + h
      0≤mh = add2-nonNeg 0≤m 0≤h

      bnd : (j : ℕ) → expPartial (m + h) j ≤ B₀
      bnd j = ≤-trans (expPartial-le-param (m + h) U₀ 0≤mh mh≤U₀ j) (bnd₀ j)

      upWin : (n : ℕ) → expPartialℝ x n ≤ℝ embedℚ (expPartial m n + W)
      upWin n = proj₂ (expPartialℝ-window m h B₀ 0≤m 0≤h m≤x x≤mh bnd n)

      tb : Σ ℕ (λ N → (∀ j → N ≤ℕ j → expPartial m N ≤ expPartial m j)
                    × (∀ j → N ≤ℕ j → expPartial m j ≤ expPartial m N + d))
      tb = exp-bracket-le m 0≤m d 0<d

      N : ℕ
      N = proj₁ tb

      tail : (j : ℕ) → N ≤ℕ j → expPartial m j ≤ expPartial m N + d
      tail = proj₂ (proj₂ tb)

      0≤d : 0ℚ ≤ d
      0≤d = <⇒≤ 0<d

      part≤ : (n : ℕ) → expPartial m n ≤ expPartial m N + d
      part≤ = expPartial-mN m 0≤m N d 0≤d tail

      dW<A : d + W < q - p
      dW<A = ≤-<-trans (+-mono-≤ (≤-refl {d}) (<⇒≤ W<d)) d+d<A

      occ : p < expPartial m N → Occupied Pℝ p
      occ p<mN =
        Pℝ-occupied-of-strict p N
          (<-≤ℝ-trans (embedℚ-mono p (expPartial m N) p<mN)
                      (expPartialℝ-≥-of-bound x m 0≤m m≤x N))

      upp : expPartial m N ≤ p → Upper Pℝ q
      upp mN≤p r (q₀ , (r≈ , n , q₀≤n)) =
        let
          mn≤pd : expPartial m n ≤ p + d
          mn≤pd = ≤-trans (part≤ n) (+-mono-≤ mN≤p (≤-refl {d}))

          sum≤ : expPartial m n + W ≤ p + (d + W)
          sum≤ = ≤-trans (+-mono-≤ mn≤pd (≤-refl {W}))
                          (≤-reflexive (+-assoc p d W))

          pdW<q : p + (d + W) < q
          pdW<q = subst (λ z → p + (d + W) < z) (plus-diff p q)
                    (+-monoʳ-< p dW<A)

          mid : embedℚ q₀ ≤ℝ embedℚ (p + (d + W))
          mid = ≤ℝ-trans q₀≤n
                  (≤ℝ-trans (upWin n)
                    (embedℚ-≤ (expPartial m n + W) (p + (d + W)) sum≤))
        in
          ≤ℝ-<trans (≤ℝ-trans (≈⇒≤ℝ r≈) mid)
            (embedℚ-mono (p + (d + W)) q pdW<q)

      order : (p < expPartial m N) ⊎ (expPartial m N ≤ p)
      order = lt-split p (expPartial m N) (<-cmp p (expPartial m N))
    in
      [ (λ lt → inj₁ (occ lt)) , (λ le → inj₂ (upp le)) ]′ order

  located : Located Pℝ
  located p q p<q =
    let
      A : ℚ
      A = q - p

      0<A : 0ℚ < A
      0<A = pos-diff p q p<q

      C : ℚ
      C = 1ℚ + B₀

      0<C : 0ℚ < C
      0<C = 0<1+B₀

      0≤C : 0ℚ ≤ C
      0≤C = <⇒≤ 0<C

      1≤C : 1ℚ ≤ C
      1≤C = subst (λ z → z ≤ C) (+-identityʳ 1ℚ) (+-mono-≤ (≤-refl {1ℚ}) 0≤B₀)

      dbl : ℚ
      dbl = C + C

      C≤dbl : C ≤ dbl
      C≤dbl = subst (λ z → z ≤ dbl) (+-identityʳ C)
                (+-mono-≤ (≤-refl {C}) 0≤C)

      arch : Σ ℕ (λ K → dbl < embed K)
      arch = let rr = archimedean (embedℚ dbl)
             in proj₁ rr , embedℚ-reflect dbl (embed (proj₁ rr)) (proj₂ rr)

      K : ℕ
      K = proj₁ arch

      dbl<K : dbl < embed K
      dbl<K = proj₂ arch

      dv : ℚ
      dv = embed (suc K)

      0<dv : 0ℚ < dv
      0<dv = 0<embed K

      K≤sucK : K ≤ℕ suc K
      K≤sucK = ℕP.m≤n⇒m≤1+n (ℕP.≤-refl {K})

      dbl≤dv : dbl ≤ dv
      dbl≤dv = ≤-trans (<⇒≤ dbl<K) (embed-mono-≤ K≤sucK)

      C≤dv : C ≤ dv
      C≤dv = ≤-trans C≤dbl dbl≤dv

      2<dv : (1ℚ + 1ℚ) < dv
      2<dv = <-≤-trans (≤-<-trans (+-mono-≤ 1≤C 1≤C) dbl<K)
                (embed-mono-≤ K≤sucK)

      r : ℚ
      r = 1/_ dv {{pos⇒nonZero dv}}

      d : ℚ
      d = A * r

      0<d : 0ℚ < d
      0<d = ÷-pos A dv {{embed-suc-pos {K}}} 0<A

      β : ℚ
      β = d * r

      0<β : 0ℚ < β
      0<β = ÷-pos d dv {{embed-suc-pos {K}}} 0<d

      βdv≡d : β * dv ≡ d
      βdv≡d = ÷-cancel d dv {{pos⇒nonZero dv}}

      small : Σ ℕ (λ k → zero ≤ℕ k × width x k < β)
      small = width-below-strict x β zero 0<β

      k : ℕ
      k = proj₁ small

      width<β : width x k < β
      width<β = proj₂ (proj₂ small)

      reciSum : r + r < 1ℚ
      reciSum = recip-add-lt-one dv {{embed-suc-pos {K}}} 2<dv

      reciA : (r + r) * A < 1ℚ * A
      reciA = *-<-mono-right (r + r) 1ℚ A reciSum 0<A

      reciA' : A * (r + r) < 1ℚ * A
      reciA' = subst (λ z → z < 1ℚ * A) (sym (*-comm A (r + r))) reciA

      reciA'' : A * (r + r) < A
      reciA'' = subst (λ z → A * (r + r) < z)
                (trans (*-comm 1ℚ A) (*-identityʳ A)) reciA'

      d+d<A : d + d < A
      d+d<A = subst (λ z → z < A) (*-distribˡ-+ A r r) reciA''

      Wbd : (hh : ℚ) → 0ℚ ≤ hh → hh ≤ width x k → hh * C < d
      Wbd hh 0≤hh hh≤w =
        let
          s1 : hh * C ≤ width x k * dv
          s1 = *-mono-≤-nonNeg 0≤hh hh≤w 0≤C C≤dv

          s2 : width x k * dv < β * dv
          s2 = *-<-mono-right (width x k) β dv width<β 0<dv

          s3 : width x k * dv < d
          s3 = subst (λ z → width x k * dv < z) βdv≡d s2
        in
          ≤-<-trans s1 s3
    in
      located-aux p q k d 0<d Wbd d+d<A (bracketAt k)

  ----------------------------------------------------------------------
  -- The least upper bound of the cut
  --
  -- 割的上确界

  -- Zero is a member: its partial sum at index zero is zero itself, so
  -- the cut is inhabited and `sup` applies with u₀ = embedℚ (B₀ + 1ℚ).
  --
  -- 零是成员：下标零处的部分和就是零本身，故割非空，`sup` 以
  -- u₀ = embedℚ (B₀ + 1ℚ) 套用。
  Pℝ-zero : Pℝ (embedℚ 0ℚ)
  Pℝ-zero = Pℝ-member 0ℚ (zero , embedℚ-≤ 0ℚ 0ℚ (≤-refl {0ℚ}))

  expℝ : RealI
  expℝ = sup located Pℝ-zero Pℝ-isUpper

  -- Every member lies below the cut, and the cut is the least such real.
  --
  -- 每个成员都在割之下，且割是满足此性质的最小实数。
  expℝ-upper : (r : RealI) → Pℝ r → r ≤ℝ expℝ
  expℝ-upper r pr = sup-upper located Pℝ-zero Pℝ-isUpper r pr

  expℝ-least : (y : RealI) → ((r : RealI) → Pℝ r → r ≤ℝ y) → expℝ ≤ℝ y
  expℝ-least y bound = sup-least located Pℝ-zero Pℝ-isUpper y bound

  ----------------------------------------------------------------------
  -- Every partial sum lies below the cut
  --
  -- 每个部分和都在割之下

  -- A rational strictly below some partial sum is itself a member of the
  -- cut, hence lies below the cut. If the cut were strictly below the
  -- partial sum, density would supply a rational squeezed in between, and
  -- that rational would both be below the cut (as a member) and above it
  -- (as the squeezed point). So the cut dominates every partial sum, which
  -- is what lets a value-level estimate at the cut be lifted to the
  -- partial sums and back.
  --
  -- 严格低于某个部分和的有理数本身就是割的成员，从而在割之下。若割严格低于
  -- 该部分和，稠密性便给出夹在中间的有理数，它作为成员在割之下、作为夹点又在
  -- 割之上。故割支配每个部分和；这正是把割处的取值估计上下搬运的依据。
  expPartialℝ-le-expℝ : (n : ℕ) → expPartialℝ x n ≤ℝ expℝ
  expPartialℝ-le-expℝ n cut<part =
    let
      win : Σ ℚ (λ q → (expℝ <ℝ embedℚ q)
                     × (embedℚ q <ℝ expPartialℝ x n))
      win = dense cut<part

      q : ℚ
      q = proj₁ win

      cut<q : expℝ <ℝ embedℚ q
      cut<q = proj₁ (proj₂ win)

      q<part : embedℚ q <ℝ expPartialℝ x n
      q<part = proj₂ (proj₂ win)

      w : Σ ℕ (λ j → embedℚ q ≤ℝ expPartialℝ x j)
      w = n , <⇒≤ℝ q<part

      member : Pℝ (embedℚ q)
      member = Pℝ-member q w

      q≤cut : embedℚ q ≤ℝ expℝ
      q≤cut = expℝ-upper (embedℚ q) member
    in
      q≤cut cut<q

  ----------------------------------------------------------------------
  -- The cut lies below any bound of the partial sums
  --
  -- 任何部分和的上界也是割的上界

  -- Each member of the cut is an embedded rational dominated by some
  -- partial sum, so a bound shared by every partial sum bounds every
  -- member, and the least upper bound inherits it. Together with
  -- `expPartialℝ-le-expℝ` this pins the cut as the least upper bound of
  -- the partial sums: below all of them, and below every common bound.
  --
  -- 割的每个成员都是被某个部分和支配的嵌入有理数，故每个部分和共有的界也界住
  -- 每个成员，最小上界因而继承该界。与 `expPartialℝ-le-expℝ` 合起来，割恰是
  -- 部分和的最小上界：在所有部分和之上，又在所有共同界之下。
  expℝ-le-of-partials : (v : RealI) → ((n : ℕ) → expPartialℝ x n ≤ℝ v)
                      → expℝ ≤ℝ v
  expℝ-le-of-partials v bound =
    expℝ-least v (λ z (q , (z≈q , (n , q≤part))) →
      ≤ℝ-trans {x = z} {y = embedℚ q} {z = v}
        (≈⇒≤ℝ z≈q)
        (≤ℝ-trans {x = embedℚ q} {y = expPartialℝ x n} {z = v}
          q≤part (bound n)))
