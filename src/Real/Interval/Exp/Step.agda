------------------------------------------------------------------------
-- The parameter step and the linear lower bound
--
-- 参数步进与线性下界
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Step where

open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _^_; _⊔_)
  renaming (_+_ to _+ℕ_)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; NonZero; _≤_; _<_; _+_; _-_; _*_; ∣_∣) renaming (-_ to neg)
open import Data.Rational.Base using (_÷_; 1/_; positive)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; <⇒≤; <-≤-trans; <-asym; +-mono-≤; +-monoˡ-<; +-identityˡ
  ; +-identityʳ; +-inverseˡ; +-inverseʳ; +-assoc; +-monoˡ-≤; +-monoʳ-≤; +-monoʳ-<
  ; neg-antimono-≤; neg-distrib-+; 1/pos⇒pos; pos⇒nonZero; positive⁻¹; +-mono-<
  ; ≤-<-trans; +-comm; *-identityʳ; *-assoc; *-distribˡ-+; *-inverseˡ
  ; pos*pos⇒pos; *-monoˡ-<-pos; ∣-p∣≡∣p∣; 0≤p⇒∣p∣≡p)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (rotate-sum; 0<1; 0≤1)
open import Real using (ε; half; embed; embed-mono-≤; 0<ε)
open import Real.Archimedean using (ε-archimedean)
open import Real.CauchyToInterval using (M; K; K≥k; μ≤M)
open import Real.Interval using (RealI)
open import Real.IntervalEquiv using (l; u; l-mono; u-mono)
open import Real.Interval using (δ; δ-pos; pos-pow; dyadic)
open import Real.Interval.ContinuityRecipBasic using (u-cauchy→realI; ε≤1)
open import Real.Interval.Exp.Core as ExpCore using
  (term; expPartial; expPartial-cauchy; expSeq; expq; expPartial-nonNeg
  ; expPartial-zero; expPartial-suc; sumQ-mono; _≤ℕ_)
open import Real.Interval.Exp.Order using (expPartial-two; term-mono)
open import Real.Interval.Exp.Lipschitz using
  (expPartial-bound; expPartial-param-bnd; le-add-right)
open import Real.Interval.Kit using (half+half≡1; recip-antitone; 0<half)
open import Real.Interval.LimitLaws using (ε-mono; abs<⇒upper)
open import Real.Interval.Node using (l-dyadic)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)

------------------------------------------------------------------------
-- L9: the parameter step lemma expq-step-up
--
-- L9：参数步进引理 expq-step-up

expq-u : (q : ℚ) (0≤q : 0ℚ ≤ q) (k : ℕ)
       → u (expq q 0≤q) k ≡ expPartial q (M (expSeq q 0≤q) k) + δ k
expq-u q 0≤q k = u-cauchy→realI (expSeq q 0≤q) k


------------------------------------------------------------------------
-- Any index beyond the modulus at level K k sits within ε (K k) of the sampled value
--
-- 超过 K k 层模数的任何下标都落在采样值的一个 ε (K k) 之内

expPartial-cauchy-upper : (p : ℚ) (0≤p : 0ℚ ≤ p) (k : ℕ) (n : ℕ)
                        → proj₁ (expPartial-cauchy p 0≤p (K k)) ≤ℕ n
                        → expPartial p n ≤ expPartial p (M (expSeq p 0≤p) k) + ε (K k)
expPartial-cauchy-upper p 0≤p k n N≤n =
  <⇒≤ (abs<⇒upper {a = expPartial p (M (expSeq p 0≤p) k)}
                   {c = expPartial p n}
                   {e = ε (K k)}
         (proj₂ (expPartial-cauchy p 0≤p (K k)) n (M (expSeq p 0≤p) k)
                N≤n (μ≤M (expSeq p 0≤p) k)))

------------------------------------------------------------------------
-- Padding the anchor by the other parameter's sampling index makes the modulus hypothesis unconditional
--
-- 用另一参数的采样下标给锚点补位，模数假设就无条件成立

anchor-ge : (r p : ℚ) (0≤r : 0ℚ ≤ r) (0≤p : 0ℚ ≤ p) (k : ℕ)
          → proj₁ (expPartial-cauchy p 0≤p (K k))
            ≤ℕ (M (expSeq p 0≤p) k ⊔ M (expSeq r 0≤r) k)
anchor-ge r p 0≤r 0≤p k =
  NatP.≤-trans (μ≤M (expSeq p 0≤p) k)
    (NatP.m≤m⊔n (M (expSeq p 0≤p) k) (M (expSeq r 0≤r) k))

------------------------------------------------------------------------
-- The gap left above expq p is positive
--
-- expq p 上端点之上剩下的间隙为正

gap-pos : (p : ℚ) (0≤p : 0ℚ ≤ p) (y : RealI) (k : ℕ)
        → u (expq p 0≤p) k < l y k
        → 0ℚ < l y k + neg (u (expq p 0≤p) k)
gap-pos p 0≤p y k gap =
  subst (λ z → z < l y k + neg (u (expq p 0≤p) k))
    (+-inverseʳ (u (expq p 0≤p) k))
    (+-monoˡ-< (neg (u (expq p 0≤p) k)) gap)

------------------------------------------------------------------------
-- The gap does not shrink as the layer grows
--
-- 层数增大时该间隙不变小

gap-mono : (p : ℚ) (0≤p : 0ℚ ≤ p) (y : RealI) {k₀ k₂ : ℕ}
         → k₀ ≤ℕ k₂
         → l y k₀ + neg (u (expq p 0≤p) k₀) ≤ l y k₂ + neg (u (expq p 0≤p) k₂)
gap-mono p 0≤p y {k₀} {k₂} k₀≤k₂ =
  +-mono-≤ (l-mono y {k₀} {k₂} k₀≤k₂)
           (neg-antimono-≤ (u-mono (expq p 0≤p) {k₀} {k₂} k₀≤k₂))

------------------------------------------------------------------------
-- A stepped parameter stays under the bound taken for p + 1
--
-- 步进后的参数仍落在为 p + 1 取的上界之内

expPartial-of-step : (p : ℚ) (0≤p : 0ℚ ≤ p) (h : ℚ) (0≤h : 0ℚ ≤ h)
                     (h≤1 : h ≤ 1ℚ) (C : ℚ)
                   → (∀ n → expPartial (p + 1ℚ) n ≤ C)
                   → ∀ n → expPartial (p + h) n ≤ C
expPartial-of-step p 0≤p h 0≤h h≤1 C Cb n =
  let 0≤ph : 0ℚ ≤ p + h
      0≤ph = subst (λ z → z ≤ p + h) (+-identityˡ 0ℚ) (+-mono-≤ 0≤p 0≤h)
      ph≤p1 : p + h ≤ p + 1ℚ
      ph≤p1 = +-mono-≤ (≤-refl {p}) h≤1
  in ≤-trans (sumQ-mono (λ i → term (p + h) i) (λ i → term (p + 1ℚ) i)
                        (λ i → term-mono (p + h) (p + 1ℚ) 0≤ph ph≤p1 i) n)
             (Cb n)

------------------------------------------------------------------------
-- Two pieces, each below half the gap, add up to less than the gap
--
-- 两块各不足间隙的一半，相加仍不足整个间隙

slack-lt : (a b g : ℚ) → a < g * half → b < g * half → a + b < g
slack-lt a b g a< b< =
  let s : a + b < g * half + g * half
      s = +-mono-< a< b<
      e : g * half + g * half ≡ g
      e = begin
        g * half + g * half  ≡⟨ sym (*-distribˡ-+ g half half) ⟩
        g * (half + half)    ≡⟨ cong (g *_) half+half≡1 ⟩
        g * 1ℚ               ≡⟨ *-identityʳ g ⟩
        g                    ∎
  in subst (λ z → a + b < z) e s

------------------------------------------------------------------------
-- Multiplying the division target back by the same positive factor recovers half the gap
--
-- 把除法目标乘回同一个正因子，就得到间隙的一半

h-mul-lt : (h C g : ℚ) (0<1C : 0ℚ < 1ℚ + C) {{nz : NonZero (1ℚ + C)}}
         → h < (g * half) ÷ (1ℚ + C) → h * (1ℚ + C) < g * half
h-mul-lt h C g 0<1C h<t =
  let rw : ((g * half) ÷ (1ℚ + C)) * (1ℚ + C) ≡ g * half
      rw = begin
        ((g * half) ÷ (1ℚ + C)) * (1ℚ + C)
          ≡⟨ *-assoc (g * half) (1/ (1ℚ + C)) (1ℚ + C) ⟩
        (g * half) * (1/ (1ℚ + C) * (1ℚ + C))
          ≡⟨ cong ((g * half) *_) (*-inverseˡ (1ℚ + C)) ⟩
        (g * half) * 1ℚ
          ≡⟨ *-identityʳ (g * half) ⟩
        g * half  ∎
  in subst (λ z → h * (1ℚ + C) < z) rw
       (*-monoˡ-<-pos (1ℚ + C) {{positive 0<1C}} h<t)

------------------------------------------------------------------------
-- Rotating an association so that the gap term comes first
--
-- 重排结合方式，把间隙项提到前面

cancel-gap : (v w : ℚ) → v + (w + neg v) ≡ w
cancel-gap v w = begin
  v + (w + neg v)  ≡⟨ sym (+-assoc v w (neg v)) ⟩
  (v + w) + neg v  ≡⟨ cong (_+ neg v) (+-comm v w) ⟩
  (w + v) + neg v  ≡⟨ +-assoc w v (neg v) ⟩
  w + (v + neg v)  ≡⟨ cong (w +_) (+-inverseʳ v) ⟩
  w + 0ℚ           ≡⟨ +-identityʳ w ⟩
  w                ∎

------------------------------------------------------------------------
-- The gap yields a small parameter step that keeps expq below y
--
-- 间隙给出使 expq 仍低于 y 的小参数步长

--   ≤ expPartial (p+h) A + δ                                    [A = M_p ⊔ M_r]
--   = u (expq p) k₂ + (ε (K k₂) + h * (1 + C))
--   < u (expq p) k₂ + g₀ ≤ u (expq p) k₂ + g₂ = l y k₂
--
-- 间隙给出一个小的参数位移，使 expq (p + h) 仍在 y 之下，链条为：
--   u (expq (p+h)) k₂ = expPartial (p+h) M_r + δ
--   ≤ expPartial p A + h * (1 + C) + δ                          [参数方向 Lipschitz]
--   ≤ expPartial p M_p + ε (K k₂) + h * (1 + C) + δ             [A ≥ μ_p (K k₂) 的柯西比较]
expq-step-up : (p : ℚ) (0≤p : 0ℚ ≤ p) (y : RealI) (k₀ : ℕ)
             → u (expq p 0≤p) k₀ < l y k₀
             → Σ ℚ (λ h → Σ (0ℚ < h) (λ _ → Σ (0ℚ ≤ p + h)
                 (λ 0≤ph → Σ ℕ (λ k₂ → u (expq (p + h) 0≤ph) k₂ < l y k₂))))
expq-step-up p 0≤p y k₀ gap =
  let g₀ = l y k₀ + neg (u (expq p 0≤p) k₀)
      0<g₀ : 0ℚ < g₀
      0<g₀ = gap-pos p 0≤p y k₀ gap
      p1 = p + 1ℚ
      0≤p1 : 0ℚ ≤ p1
      0≤p1 = subst (λ z → z ≤ p1) (+-identityˡ 0ℚ) (+-mono-≤ 0≤p 0≤1)
      w = expPartial-bound p1 0≤p1 (ε zero) (0<ε zero)
      C = proj₁ w
      Cb = proj₂ w
      0≤C : 0ℚ ≤ C
      0≤C = ≤-trans (expPartial-nonNeg p1 0≤p1 zero) (Cb zero)
      0<1C : 0ℚ < 1ℚ + C
      0<1C = <-≤-trans 0<1 (le-add-right 1ℚ C 0≤C)
      nz1 : NonZero (1ℚ + C)
      nz1 = pos⇒nonZero (1ℚ + C) {{positive 0<1C}}
      inv1C = 1/_ (1ℚ + C) ⦃ nz1 ⦄
      0<inv1C : 0ℚ < inv1C
      0<inv1C = positive⁻¹ inv1C {{1/pos⇒pos (1ℚ + C) {{positive 0<1C}}}}
      t₁ = g₀ * half
      0<t₁ : 0ℚ < t₁
      0<t₁ = positive⁻¹ t₁ {{pos*pos⇒pos g₀ {{positive 0<g₀}} half {{positive 0<half}}}}
      t₂ = t₁ * inv1C
      0<t₂ : 0ℚ < t₂
      0<t₂ = positive⁻¹ t₂
        {{pos*pos⇒pos t₁ {{positive 0<t₁}} inv1C {{positive 0<inv1C}}}}
      a₁ = ε-archimedean t₁ 0<t₁
      a₂ = ε-archimedean t₂ 0<t₂
      m₁ = proj₁ a₁
      m₂ = proj₁ a₂
      h = ε m₂
      0≤h : 0ℚ ≤ h
      0≤h = <⇒≤ (0<ε m₂)
      h≤1 : h ≤ 1ℚ
      h≤1 = ε≤1 m₂
      k₂ = (m₁ ⊔ m₂) +ℕ k₀
      k₀≤k₂ : k₀ ≤ℕ k₂
      k₀≤k₂ = subst (λ z → k₀ ≤ℕ z) (NatP.+-comm k₀ (m₁ ⊔ m₂))
                (NatP.m≤m+n k₀ (m₁ ⊔ m₂))
      m₁≤Kk₂ : m₁ ≤ℕ K k₂
      m₁≤Kk₂ = NatP.≤-trans
                 (NatP.≤-trans (NatP.m≤m⊔n m₁ m₂) (NatP.m≤m+n (m₁ ⊔ m₂) k₀))
                 (K≥k k₂)
      εK<t₁ : ε (K k₂) < t₁
      εK<t₁ = ≤-<-trans (ε-mono {m₁} {K k₂} m₁≤Kk₂) (proj₂ a₁)
      hC<t₁ : h * (1ℚ + C) < t₁
      hC<t₁ = h-mul-lt h C g₀ 0<1C {{nz1}} (proj₂ a₂)
      slack : ε (K k₂) + h * (1ℚ + C) < g₀
      slack = slack-lt (ε (K k₂)) (h * (1ℚ + C)) g₀ εK<t₁ hC<t₁
      0≤ph : 0ℚ ≤ p + h
      0≤ph = subst (λ z → z ≤ p + h) (+-identityˡ 0ℚ) (+-mono-≤ 0≤p 0≤h)
      Mpr = M (expSeq p 0≤p) k₂
      Mr = M (expSeq (p + h) 0≤ph) k₂
      A = Mpr ⊔ Mr
      up = u (expq p 0≤p) k₂
      g₂ = l y k₂ + neg up
      Mr≤A : Mr ≤ℕ A
      Mr≤A = NatP.m≤n⊔m Mpr Mr
      s1 : expPartial (p + h) Mr ≤ expPartial (p + h) A
      s1 = ExpCore.expPartial-le (p + h) 0≤ph Mr A Mr≤A
      s2 : expPartial (p + h) A ≤ expPartial p A + h * (1ℚ + C)
      s2 = expPartial-param-bnd p h 0≤p 0≤h A C
             (expPartial-of-step p 0≤p h 0≤h h≤1 C Cb)
      N≤A : proj₁ (expPartial-cauchy p 0≤p (K k₂)) ≤ℕ A
      N≤A = anchor-ge (p + h) p 0≤ph 0≤p k₂
      s3 : expPartial p A ≤ expPartial p Mpr + ε (K k₂)
      s3 = expPartial-cauchy-upper p 0≤p k₂ A N≤A
      T = ((expPartial p Mpr + ε (K k₂)) + h * (1ℚ + C)) + δ k₂
      c1 : expPartial (p + h) Mr + δ k₂ ≤ expPartial (p + h) A + δ k₂
      c1 = +-monoˡ-≤ (δ k₂) s1
      c2 : expPartial (p + h) A + δ k₂
         ≤ (expPartial p A + h * (1ℚ + C)) + δ k₂
      c2 = +-monoˡ-≤ (δ k₂) s2
      c3 : (expPartial p A + h * (1ℚ + C)) + δ k₂ ≤ T
      c3 = +-monoˡ-≤ (δ k₂) (+-monoˡ-≤ (h * (1ℚ + C)) s3)
      uR = expq-u (p + h) 0≤ph k₂
      uP = expq-u p 0≤p k₂
      cAll : expPartial (p + h) Mr + δ k₂ ≤ T
      cAll = ≤-trans c1 (≤-trans c2 c3)
      FINAL1 : u (expq (p + h) 0≤ph) k₂ ≤ T
      FINAL1 = subst (λ z → z ≤ T) (sym uR) cAll
      rot : T ≡ (expPartial p Mpr + δ k₂) + (ε (K k₂) + h * (1ℚ + C))
      rot = rotate-sum (expPartial p Mpr) (ε (K k₂)) (h * (1ℚ + C)) (δ k₂)
      up-slack : up + (ε (K k₂) + h * (1ℚ + C)) < up + g₂
      up-slack = <-≤-trans (+-monoʳ-< up slack)
                           (+-monoʳ-≤ up (gap-mono p 0≤p y k₀≤k₂))
      up-lt : (expPartial p Mpr + δ k₂) + (ε (K k₂) + h * (1ℚ + C)) < up + g₂
      up-lt = subst (λ z → z + (ε (K k₂) + h * (1ℚ + C)) < up + g₂)
                uP up-slack
      FINAL0 : T < up + g₂
      FINAL0 = subst (λ z → z < up + g₂) (sym rot) up-lt
      uproof : u (expq (p + h) 0≤ph) k₂ < l y k₂
      uproof = subst (λ z → u (expq (p + h) 0≤ph) k₂ < z)
                 (cancel-gap up (l y k₂)) (≤-<-trans FINAL1 FINAL0)
  in h , 0<ε m₂ , 0≤ph , (k₂ , uproof)

------------------------------------------------------------------------
-- Linear growth of expq
--
-- 线性增长：expq 的下界

--   u (expq q) k = expPartial q (M k) + δ k
--   l (dyadic (1+q) 0) k = neg (δ k) + (1 + q)
--   1 + q ≤ expPartial q (M k) + (δ k + δ k)                     (★)
-- This is what Log/Core needs for its upper bound: log only rises to
-- infinity because expq grows at least linearly. The level bound (★) comes
-- from a case split on M k, and each case uses ε (K k) ≤ δ k, that is
-- ε (K k) = 1/embed (1 + K k) and δ k = 1/embed (2 ^ suc k) with
-- 2 ^ suc k ≤ K k ≤ suc (K k) after taking reciprocals.
--
--   u (expq q) k = expPartial q (M k) + δ k
--   l (dyadic (1+q) 0) k = neg (δ k) + (1 + q)
--   1 + q ≤ expPartial q (M k) + (δ k + δ k)                     (★)
-- 这是 Log/Core 的上界所需：log 之所以趋于无穷，正因为 expq 至少线性增长。
-- dyadic (1 + q) 0 ≤ℝ expq q 即 expq q 不可能小于 dyadic (1 + q) 0；取见证
-- 层 k，把 expq 的上端点与 dyadic 的下端点都用公式展开后，(★) 归结为对
-- M k 分三种情形：M = 0、M = 1 由柯西性分别给出 1+q < ε (K k) 与
-- q < ε (K k)，M ≥ 2 由 expPartial-two 与下标单调性给出
-- 1+q ≤ expPartial q (M k)；三种情形都用 ε (K k) ≤ δ k，其中
-- ε (K k) = 1/embed (1 + K k)，δ k = 1/embed (2 ^ suc k)，而
-- 2 ^ suc k ≤ K k ≤ suc (K k)，取倒数即得。
ε-K≤δ : (k : ℕ) → ε (K k) ≤ δ k
ε-K≤δ k =
  let le : 2 ^ suc k ≤ℕ suc (K k)
      le = NatP.≤-trans (NatP.m≤n*m (2 ^ suc k) 2)
             (NatP.m≤n⇒m≤1+n {m = K k} {n = K k} NatP.≤-refl)
      0<a : 0ℚ < embed (2 ^ suc k)
      0<a = positive⁻¹ (embed (2 ^ suc k)) {{pos-pow k}}
  in recip-antitone 0<a (embed-mono-≤ le)

------------------------------------------------------------------------
-- Two absolute-value identities
--
-- 两个绝对值公式

abs-zero : (q : ℚ) (0≤q : 0ℚ ≤ q) → ∣ 0ℚ - (1ℚ + q) ∣ ≡ 1ℚ + q
abs-zero q 0≤q = begin
  ∣ 0ℚ - (1ℚ + q) ∣  ≡⟨ cong ∣_∣ (+-identityˡ (neg (1ℚ + q))) ⟩
  ∣ neg (1ℚ + q) ∣   ≡⟨ ∣-p∣≡∣p∣ (1ℚ + q) ⟩
  ∣ 1ℚ + q ∣         ≡⟨ 0≤p⇒∣p∣≡p 0≤1q ⟩
  1ℚ + q             ∎
  where
  0≤1q : 0ℚ ≤ 1ℚ + q
  0≤1q = ≤-trans 0≤1 (le-add-right 1ℚ q 0≤q)

abs-one : (q : ℚ) (0≤q : 0ℚ ≤ q) → ∣ 1ℚ - (1ℚ + q) ∣ ≡ q
abs-one q 0≤q = begin
  ∣ 1ℚ - (1ℚ + q) ∣  ≡⟨ cong ∣_∣ e ⟩
  ∣ neg q ∣          ≡⟨ ∣-p∣≡∣p∣ q ⟩
  ∣ q ∣              ≡⟨ 0≤p⇒∣p∣≡p 0≤q ⟩
  q                  ∎
  where
  e : 1ℚ - (1ℚ + q) ≡ neg q
  e = begin
    1ℚ - (1ℚ + q)          ≡⟨ cong (1ℚ +_) (neg-distrib-+ 1ℚ q) ⟩
    1ℚ + (neg 1ℚ + neg q)  ≡⟨ sym (+-assoc 1ℚ (neg 1ℚ) (neg q)) ⟩
    (1ℚ + neg 1ℚ) + neg q  ≡⟨ cong (_+ neg q) (+-inverseʳ 1ℚ) ⟩
    0ℚ + neg q             ≡⟨ +-identityˡ (neg q) ⟩
    neg q                  ∎

------------------------------------------------------------------------
-- A lower bound for M k ≥ 2
--
-- M k ≥ 2 时的下界

partial-ge-two : (q : ℚ) (0≤q : 0ℚ ≤ q) (m : ℕ) → 2 ≤ℕ m
               → 1ℚ + q ≤ expPartial q m
partial-ge-two q 0≤q m 2≤m =
  subst (λ z → z ≤ expPartial q m) (expPartial-two q)
    (ExpCore.expPartial-le q 0≤q (suc (suc zero)) m 2≤m)

------------------------------------------------------------------------
-- Reordering the sum: neg x + (y + x) ≡ y
--
-- 加法重排：neg x + (y + x) ≡ y

neg-cancel : (x y : ℚ) → neg x + (y + x) ≡ y
neg-cancel x y = begin
  neg x + (y + x)  ≡⟨ sym (+-assoc (neg x) y x) ⟩
  (neg x + y) + x  ≡⟨ cong (_+ x) (+-comm (neg x) y) ⟩
  (y + neg x) + x  ≡⟨ +-assoc y (neg x) x ⟩
  y + (neg x + x)  ≡⟨ cong (y +_) (+-inverseˡ x) ⟩
  y + 0ℚ           ≡⟨ +-identityʳ y ⟩
  y                ∎

------------------------------------------------------------------------
-- Two non-negativity lemmas for δ
--
-- δ 的两个非负性小工具

0≤δ : (k : ℕ) → 0ℚ ≤ δ k
0≤δ k = <⇒≤ (δ-pos k)

δ≤δ+δ : (k : ℕ) → δ k ≤ δ k + δ k
δ≤δ+δ k =
  subst (λ z → z ≤ δ k + δ k) (+-identityʳ (δ k))
    (+-mono-≤ (≤-refl {δ k}) (0≤δ k))

0≤δ+δ : (k : ℕ) → 0ℚ ≤ δ k + δ k
0≤δ+δ k =
  subst (λ z → z ≤ δ k + δ k) (+-identityˡ 0ℚ)
    (+-mono-≤ (0≤δ k) (0≤δ k))

------------------------------------------------------------------------
-- (★) keeping the value of M apart from its bound
--
-- (★) 主引理：M 的取值与其界分离

expPartial-suc-zero : (q : ℚ) → expPartial q (suc zero) ≡ 1ℚ
expPartial-suc-zero q = begin
  expPartial q (suc zero)          ≡⟨ expPartial-suc q zero ⟩
  expPartial q zero + term q zero  ≡⟨ cong (_+ term q zero) (expPartial-zero q) ⟩
  0ℚ + term q zero                 ≡⟨ +-identityˡ (term q zero) ⟩
  term q zero                      ∎

-- Abstracting over M (expSeq q 0≤q) k copies the expSeq record literal
-- (and the expPartial-cauchy term inside it) into every branch, which
-- --double-check then re-expands repeatedly; this blew up memory. So the
-- value m and the bound N ≤ m are passed separately and the case split
-- runs on a plain natural number.
--
-- 直接对 M (expSeq q 0≤q) k 做 with 抽象，会把 expSeq 记录字面量连同其中的
-- expPartial-cauchy 项复制进每个分支；--double-check 重检这些分支时反复
-- 展开，实测内存失控。故此处把取值 m 与它的柯西模界 N ≤ m 分开传入。
partial-lower : (q : ℚ) (0≤q : 0ℚ ≤ q) (k N : ℕ) (m : ℕ)
              → N ≡ proj₁ (expPartial-cauchy q 0≤q (K k))
              → N ≤ℕ m
              → 1ℚ + q ≤ expPartial q m + (δ k + δ k)
partial-lower q 0≤q k N zero refl N≤0 =
  let C = proj₂ (expPartial-cauchy q 0≤q (K k))
      N≤2 : N ≤ℕ suc (suc zero)
      N≤2 = NatP.≤-trans N≤0 z≤n
      h : ∣ expPartial q zero - expPartial q (suc (suc zero)) ∣ < ε (K k)
      h = C zero (suc (suc zero)) N≤0 N≤2
      s1 : ∣ 0ℚ - expPartial q (suc (suc zero)) ∣ < ε (K k)
      s1 = subst (λ z → ∣ z - expPartial q (suc (suc zero)) ∣ < ε (K k))
             (expPartial-zero q) h
      s2 : ∣ 0ℚ - (1ℚ + q) ∣ < ε (K k)
      s2 = subst (λ z → ∣ 0ℚ - z ∣ < ε (K k)) (expPartial-two q) s1
      s3 : 1ℚ + q < ε (K k)
      s3 = subst (λ z → z < ε (K k)) (abs-zero q 0≤q) s2
      s4 : 1ℚ + q < δ k
      s4 = <-≤-trans s3 (ε-K≤δ k)
      le : 1ℚ + q ≤ δ k + δ k
      le = ≤-trans (<⇒≤ s4) (δ≤δ+δ k)
      le' : 1ℚ + q ≤ 0ℚ + (δ k + δ k)
      le' = subst (λ z → 1ℚ + q ≤ z) (sym (+-identityˡ (δ k + δ k))) le
  in subst (λ z → 1ℚ + q ≤ z + (δ k + δ k)) (sym (expPartial-zero q)) le'
partial-lower q 0≤q k N (suc zero) refl N≤1 =
  let C = proj₂ (expPartial-cauchy q 0≤q (K k))
      N≤2 : N ≤ℕ suc (suc zero)
      N≤2 = NatP.≤-trans N≤1 (s≤s z≤n)
      h : ∣ expPartial q (suc zero) - expPartial q (suc (suc zero)) ∣
          < ε (K k)
      h = C (suc zero) (suc (suc zero)) N≤1 N≤2
      s1 : ∣ 1ℚ - expPartial q (suc (suc zero)) ∣ < ε (K k)
      s1 = subst (λ z → ∣ z - expPartial q (suc (suc zero)) ∣ < ε (K k))
             (expPartial-suc-zero q) h
      s2 : ∣ 1ℚ - (1ℚ + q) ∣ < ε (K k)
      s2 = subst (λ z → ∣ 1ℚ - z ∣ < ε (K k)) (expPartial-two q) s1
      s3 : q < ε (K k)
      s3 = subst (λ z → z < ε (K k)) (abs-one q 0≤q) s2
      s4 : q < δ k
      s4 = <-≤-trans s3 (ε-K≤δ k)
      le : 1ℚ + q ≤ 1ℚ + (δ k + δ k)
      le = +-mono-≤ (≤-refl {1ℚ}) (≤-trans (<⇒≤ s4) (δ≤δ+δ k))
  in subst (λ z → 1ℚ + q ≤ z + (δ k + δ k)) (sym (expPartial-suc-zero q)) le
partial-lower q 0≤q k N (suc (suc n)) refl N≤m =
  let le-ge : 1ℚ + q ≤ expPartial q (suc (suc n))
      le-ge = partial-ge-two q 0≤q (suc (suc n)) (s≤s (s≤s z≤n))
      le' : expPartial q (suc (suc n))
          ≤ expPartial q (suc (suc n)) + (δ k + δ k)
      le' = subst (λ z → z ≤ expPartial q (suc (suc n)) + (δ k + δ k))
              (+-identityʳ (expPartial q (suc (suc n))))
              (+-mono-≤ (≤-refl {expPartial q (suc (suc n))}) (0≤δ+δ k))
  in ≤-trans le-ge le'

M-lower : (q : ℚ) (0≤q : 0ℚ ≤ q) (k : ℕ)
        → 1ℚ + q ≤ expPartial q (M (expSeq q 0≤q) k) + (δ k + δ k)
M-lower q 0≤q k =
  partial-lower q 0≤q k (proj₁ (expPartial-cauchy q 0≤q (K k)))
    (M (expSeq q 0≤q) k) refl (μ≤M (expSeq q 0≤q) k)

------------------------------------------------------------------------
-- A linear lower bound: dyadic (1 + q) 0 ≤ℝ expq q
--
-- 线性下界：dyadic (1 + q) 0 ≤ℝ expq q

expq-ge-linear : (q : ℚ) (0≤q : 0ℚ ≤ q) → dyadic (1ℚ + q) 0 ≤ℝ expq q 0≤q
expq-ge-linear q 0≤q (k , hlt) =
  let Mq = M (expSeq q 0≤q) k
      uP : u (expq q 0≤q) k ≡ expPartial q Mq + δ k
      uP = expq-u q 0≤q k
      lE : l (dyadic (1ℚ + q) 0) k ≡ neg (δ k) + (1ℚ + q)
      lE = l-dyadic (1ℚ + q) k
      h1a : u (expq q 0≤q) k < neg (δ k) + (1ℚ + q)
      h1a = subst (λ z → u (expq q 0≤q) k < z) lE hlt
      h1 : expPartial q Mq + δ k < neg (δ k) + (1ℚ + q)
      h1 = subst (λ z → z < neg (δ k) + (1ℚ + q)) uP h1a
      h2 : (expPartial q Mq + δ k) + δ k
         < (neg (δ k) + (1ℚ + q)) + δ k
      h2 = +-monoˡ-< (δ k) h1
      rw : (neg (δ k) + (1ℚ + q)) + δ k ≡ 1ℚ + q
      rw = trans (+-assoc (neg (δ k)) (1ℚ + q) (δ k))
             (neg-cancel (δ k) (1ℚ + q))
      h3 : (expPartial q Mq + δ k) + δ k < 1ℚ + q
      h3 = subst (λ z → (expPartial q Mq + δ k) + δ k < z) rw h2
      as : (expPartial q Mq + δ k) + δ k ≡ expPartial q Mq + (δ k + δ k)
      as = +-assoc (expPartial q Mq) (δ k) (δ k)
      h3' : expPartial q Mq + (δ k + δ k) < 1ℚ + q
      h3' = subst (λ z → z < 1ℚ + q) as h3
      ge : 1ℚ + q ≤ expPartial q Mq + (δ k + δ k)
      ge = M-lower q 0≤q k
      bad : 1ℚ + q < 1ℚ + q
      bad = ≤-<-trans ge h3'
  in <-asym bad bad
