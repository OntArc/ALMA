------------------------------------------------------------------------
-- Crossing a rational window
--
-- 穿过有理窗口
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Cross where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Nat.Properties as NatP using ()
open import Data.Product using (Σ; _×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_; _-_; _*_)
open import Data.Rational.Base using (Positive; positive; -_)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; <⇒≤; ≤⇒≯; <-asym; <-irrefl; <-≤-trans; ≤-<-trans; +-mono-≤
  ; +-monoˡ-≤; +-monoˡ-<; +-monoʳ-<; +-assoc; +-comm; +-identityʳ; *-assoc
  ; *-comm; *-identityʳ; *-distribˡ-+; *-zeroˡ; pos*pos⇒pos; positive⁻¹; <-cmp)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong; trans; subst)
open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)

open import Base.RationalRing using (0<1; 0≤1; neg-0)
open import Real using (half)
open import Real.IntervalEquiv using (recipPow2)
open import Real.Interval using (embedℚ)
open import Real.Interval.Continuity using (embedℚ-mono)
open import Real.Interval.Equiv using (≈ℝ-sym)
open import Real.Interval.Exp.Core using
  (expPartial; expq; exp-bracket-le; expPartial-le; expPartial-nonNeg; _≤ℕ_)
open import Real.Interval.Exp.Order using
  (expPartial-one-le; expPartial-two; expPartial-le-param)
open import Real.Interval.Exp.Lipschitz using (expPartial-param-bnd)
open import Real.Interval.Exp.PartialLe using (expPartial-le-expq)
open import Real.Interval.Exp.Bracket using (expq-le-of-tail)
open import Real.Interval.Exp.Bisect using (Bracket; bisect)
open import Real.Interval.Exp.Uniform using
  (tail-transfer; expPartial-bound-of-tail)
open import Real.Interval.Exp.Full using (expq-total; expq-total-nonNeg)
open import Real.Interval.Kit using
  (0<half; half+half≡1; *-mono-≤-nonNeg; tail-bound)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)
open import Real.Interval.OrderLe using (≈⇒≤ℝ; <-≤ℝ-trans; ≤ℝ-<trans)
open import Real.Interval.Rational using (pos-diff; plus-diff)
open import Real.Interval.Series.Bounds using (le-self-add)

------------------------------------------------------------------------
-- Small rational and arithmetic facts
--
-- 有理数与算术的小事实

-- Subtracting zero changes nothing.
--
-- 减去零不改变被减数。
p-0 : (p : ℚ) → p - 0ℚ ≡ p
p-0 p = trans (cong (p +_) neg-0) (+-identityʳ p)

-- Adding a positive strictly grows.
--
-- 加上一个正数严格变大。
lt-self-add : (p q : ℚ) → 0ℚ < q → p < p + q
lt-self-add p q 0<q =
  subst (λ z → z < p + q) (+-identityʳ p) (+-monoʳ-< p 0<q)

------------------------------------------------------------------------
-- Two-step slack for naturals
--
-- 自然数的两步松弛

n≤ssn : (n : ℕ) → n ≤ℕ suc (suc n)
n≤ssn zero = z≤n
n≤ssn (suc n) = s≤s (n≤ssn n)

------------------------------------------------------------------------
-- Deciding `t ≤ N`, and the two stable forms
--
-- 判定 `t ≤ N` 及两个稳定性形式

-- `_≤_` on ℚ is not `¬ (flip _<_)`, so the three-way comparison has to be
-- folded into the shapes actually needed: a certificate of `¬ (N < t)`
-- (which is `t ≤ N` up to a Tri elimination), a proof of `¬¬ (a < b)`,
-- and `¬ (b ≤ a) ⇒ a < b`.
--
-- ℚ 的 `_≤_` 不是 `¬ (flip _<_)`，故三分比较要折成真正用到的三种形状：
-- `¬ (N < t)` 的证书（消去 Tri 后即 `t ≤ N`）、`¬¬ (a < b)` 的证明、
-- 以及 `¬ (b ≤ a) ⇒ a < b`。
tri-split : (t N : ℚ) → Tri (t < N) (t ≡ N) (N < t)
          → ((N < t) → ⊥) ⊎ (((N < t) → ⊥) → ⊥)
tri-split t N (tri< t<N _ _) = inj₁ (<-asym t<N)
tri-split t N (tri≈ _ t≡N _) =
  inj₁ (λ N<t → <-irrefl refl (subst (λ z → z < t) (sym t≡N) N<t))
tri-split t N (tri> _ _ N<t) = inj₂ (λ f → f N<t)

not-gt-le : (t N : ℚ) → Tri (t < N) (t ≡ N) (N < t) → ((N < t) → ⊥) → t ≤ N
not-gt-le t N (tri< t<N _ _) _ = <⇒≤ t<N
not-gt-le t N (tri≈ _ t≡N _) _ = subst (λ z → t ≤ z) t≡N (≤-refl {t})
not-gt-le t N (tri> _ _ N<t) nh = ⊥-elim (nh N<t)

-- The rational order is discrete: `¬¬ (a < b)` yields `a < b`. The two
-- stable forms above are rebuilt here rather than imported from `Log/Full`
-- so that the Exp layer stays clear of the Log layer, which will later
-- depend on this module for strictness.
--
-- 有理序是离散的：`¬¬ (a < b)` 给出 `a < b`：上述两个稳定形式在本地重建，
-- 以免 Exp 层依赖 Log 层——后续 log 的严格单调性要反过来依赖本模块。
notnot-lt : (a b : ℚ) → Tri (a < b) (a ≡ b) (b < a)
          → (((a < b) → ⊥) → ⊥) → a < b
notnot-lt a b (tri< a<b _ _) _ = a<b
notnot-lt a b (tri≈ _ a≡b _) nn =
  ⊥-elim (nn (λ a<b → <-irrefl refl (subst (λ z → z < b) a≡b a<b)))
notnot-lt a b (tri> _ _ b<a) nn = ⊥-elim (nn (<-asym b<a))

------------------------------------------------------------------------
-- The crossing, with the window width given
--
-- 给定窗口余量的跨越

expq-cross-of-d : (r₁ r₂ d : ℚ) (1≤r₁ : 1ℚ ≤ r₁) (r₁<r₂ : r₁ < r₂)
                  (0<d : 0ℚ < d) (gap-eq : d + d ≡ r₂ - r₁)
                → Σ ℚ (λ q → (embedℚ r₁ <ℝ expq-total q)
                           × (expq-total q <ℝ embedℚ r₂))
expq-cross-of-d r₁ r₂ d 1≤r₁ r₁<r₂ 0<d gap-eq =
  let
    0≤r₁ : 0ℚ ≤ r₁
    0≤r₁ = ≤-trans 0≤1 1≤r₁

    0<r₁ : 0ℚ < r₁
    0<r₁ = <-≤-trans 0<1 1≤r₁

    N₀ , (mono₀ , tail₀) = exp-bracket-le r₁ 0≤r₁ d 0<d

    N : ℕ
    N = suc (suc N₀)

    N₀≤N : N₀ ≤ℕ N
    N₀≤N = n≤ssn N₀

    1≤N : 1 ≤ℕ N
    1≤N = s≤s (z≤n {suc N₀})

    2≤N : suc (suc zero) ≤ℕ N
    2≤N = s≤s (s≤s (z≤n {N₀}))

    PNQ : ℚ
    PNQ = expPartial r₁ N

    CL : ℚ
    CL = PNQ + d

    L : ℚ
    L = 1ℚ + CL

    C : ℚ
    C = r₁ * L

    -- The tail certificate at index N, at the left end of the window.
    --
    -- 指标 N 处的尾界证书，位于窗口左端。
    certQ : (m : ℕ) → N ≤ℕ m → expPartial r₁ m ≤ expPartial r₁ N + d
    certQ m N≤m =
      ≤-trans (tail₀ m (NatP.≤-trans N₀≤N N≤m))
              (+-monoˡ-≤ d (expPartial-le r₁ 0≤r₁ N₀ N N₀≤N))

    0≤PNQ : 0ℚ ≤ PNQ
    0≤PNQ = expPartial-nonNeg r₁ 0≤r₁ N

    0≤CL : 0ℚ ≤ CL
    0≤CL = ≤-trans 0≤PNQ (le-self-add {p = PNQ} {q = d} (<⇒≤ 0<d))

    0≤L : 0ℚ ≤ L
    0≤L = ≤-trans 0≤1 (le-self-add {p = 1ℚ} {q = CL} 0≤CL)

    0≤C : 0ℚ ≤ C
    0≤C = subst (λ z → z ≤ C) (*-zeroˡ 0ℚ)
            (*-mono-≤-nonNeg {a = 0ℚ} {a' = r₁} {b = 0ℚ} {b' = L}
              (≤-refl {0ℚ}) 0≤r₁ (≤-refl {0ℚ}) 0≤L)

    n , hn = tail-bound C 0≤C d 0<d

    P : ℚ → Set
    P = λ x → (r₁ < expPartial x N) → ⊥

    split : (x : ℚ) → P x ⊎ ((P x) → ⊥)
    split x = tri-split (expPartial x N) r₁ (<-cmp (expPartial x N) r₁)

    P0 : P 0ℚ
    P0 = subst (λ z → (r₁ < z) → ⊥) (sym (expPartial-one-le N 1≤N)) (≤⇒≯ 1≤r₁)

    lt-succ : r₁ < 1ℚ + r₁
    lt-succ = subst (λ z → r₁ < z) (+-comm r₁ 1ℚ) (lt-self-add r₁ 1ℚ 0<1)

    PN-le : 1ℚ + r₁ ≤ PNQ
    PN-le = subst (λ z → z ≤ PNQ) (expPartial-two r₁)
             (expPartial-le r₁ 0≤r₁ (suc (suc zero)) N 2≤N)

    r₁<PN : r₁ < PNQ
    r₁<PN = <-≤-trans lt-succ PN-le

    nb : P r₁ → ⊥
    nb = λ f → f r₁<PN

    bis : Bracket P 0ℚ r₁ n
    bis = bisect P split 0ℚ r₁ 0<r₁ P0 nb n

    b , h , Pb , nPb , bh≤r₁ , 0≤h , 0≤b , heq = bis

    bh : ℚ
    bh = b + h

    0≤bh : 0ℚ ≤ bh
    0≤bh = ≤-trans 0≤b (le-self-add {p = b} {q = h} 0≤h)

    -- The bisected width is `r₁ * recipPow2 n`.
    --
    -- 折半后的宽度就是 `r₁ * recipPow2 n`。
    heq' : h ≡ r₁ * recipPow2 n
    heq' = trans heq (cong (_* recipPow2 n) (p-0 r₁))

    hL-eq : h * L ≡ C * recipPow2 n
    hL-eq = trans (cong (_* L) heq')
              (trans (*-assoc r₁ (recipPow2 n) L)
                (trans (cong (r₁ *_) (*-comm (recipPow2 n) L))
                  (sym (*-assoc r₁ L (recipPow2 n)))))

    hL<d : h * L < d
    hL<d = subst (λ z → z < d) (sym hL-eq) (hn n NatP.≤-refl)

    -- The tail bound at the final point, transferred from the left end.
    --
    -- 终点处的尾界，从左侧传递而来。
    certBh : (m : ℕ) → N ≤ℕ m → expPartial bh m ≤ expPartial bh N + d
    certBh = tail-transfer bh r₁ 0≤bh bh≤r₁ N d 0<d certQ

    bndBh : (j : ℕ) → expPartial bh j ≤ CL
    bndBh j =
      ≤-trans (expPartial-bound-of-tail bh r₁ 0≤bh bh≤r₁ N d 0<d certQ j)
              (+-monoˡ-≤ d (expPartial-le-param bh r₁ 0≤bh bh≤r₁ N))

    lip : expPartial bh N ≤ expPartial b N + h * L
    lip = expPartial-param-bnd b h 0≤b 0≤h N CL bndBh

    PNb≤r₁ : expPartial b N ≤ r₁
    PNb≤r₁ = not-gt-le (expPartial b N) r₁ (<-cmp (expPartial b N) r₁) Pb

    bndBH : expPartial bh N ≤ r₁ + h * L
    bndBH = ≤-trans lip (+-monoˡ-≤ (h * L) PNb≤r₁)

    step1 : expPartial bh N + d ≤ (r₁ + h * L) + d
    step1 = +-monoˡ-≤ d bndBH

    step2 : (r₁ + h * L) + d < (r₁ + d) + d
    step2 = +-monoˡ-< d (+-monoʳ-< r₁ hL<d)

    step3 : (r₁ + d) + d ≡ r₂
    step3 = trans (+-assoc r₁ d d)
              (trans (cong (r₁ +_) gap-eq) (plus-diff r₁ r₂))

    arith : expPartial bh N + d < r₂
    arith = subst (λ z → expPartial bh N + d < z) step3 (≤-<-trans step1 step2)

    upper₁ : expq bh 0≤bh ≤ℝ embedℚ (expPartial bh N + d)
    upper₁ = expq-le-of-tail bh 0≤bh N d 0<d certBh

    upper₂ : embedℚ (expPartial bh N + d) <ℝ embedℚ r₂
    upper₂ = embedℚ-mono (expPartial bh N + d) r₂ arith

    upper : expq bh 0≤bh <ℝ embedℚ r₂
    upper = ≤ℝ-<trans upper₁ upper₂

    -- Below: `P N` has crossed `r₁` at the final point.
    --
    -- 下侧：`P N` 在终点越过了 `r₁`。
    mp : r₁ < expPartial bh N
    mp = notnot-lt r₁ (expPartial bh N) (<-cmp r₁ (expPartial bh N)) nPb

    lower₁ : embedℚ r₁ <ℝ embedℚ (expPartial bh N)
    lower₁ = embedℚ-mono r₁ (expPartial bh N) mp

    lower₂ : embedℚ (expPartial bh N) ≤ℝ expq bh 0≤bh
    lower₂ = expPartial-le-expq bh 0≤bh N

    lower : embedℚ r₁ <ℝ expq bh 0≤bh
    lower = <-≤ℝ-trans lower₁ lower₂

    lower-total : embedℚ r₁ <ℝ expq-total bh
    lower-total = <-≤ℝ-trans lower (≈⇒≤ℝ (≈ℝ-sym (expq-total-nonNeg bh 0≤bh)))

    upper-total : expq-total bh <ℝ embedℚ r₂
    upper-total = ≤ℝ-<trans (≈⇒≤ℝ (expq-total-nonNeg bh 0≤bh)) upper
  in
    bh , (lower-total , upper-total)

------------------------------------------------------------------------
-- The crossing over a window above one
--
-- 一以上窗口的跨越

expq-cross-above : (r₁ r₂ : ℚ) (1≤r₁ : 1ℚ ≤ r₁) (r₁<r₂ : r₁ < r₂)
                 → Σ ℚ (λ q → (embedℚ r₁ <ℝ expq-total q)
                            × (expq-total q <ℝ embedℚ r₂))
expq-cross-above r₁ r₂ 1≤r₁ r₁<r₂ =
  let
    gap : ℚ
    gap = r₂ - r₁

    0<gap : 0ℚ < gap
    0<gap = pos-diff r₁ r₂ r₁<r₂

    d : ℚ
    d = gap * half

    0<d : 0ℚ < d
    0<d = positive⁻¹ d
            ⦃ pos*pos⇒pos gap ⦃ positive 0<gap ⦄ half ⦃ positive 0<half ⦄ ⦄

    gap-eq : d + d ≡ r₂ - r₁
    gap-eq = trans (sym (*-distribˡ-+ gap half half))
               (trans (cong (gap *_) half+half≡1) (*-identityʳ gap))
  in
    expq-cross-of-d r₁ r₂ d 1≤r₁ r₁<r₂ 0<d gap-eq
