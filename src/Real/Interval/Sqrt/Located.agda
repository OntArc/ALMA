------------------------------------------------------------------------
-- Locatedness of the square-root cut
--
-- 平方根割的定位性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Sqrt.Located where

open import Data.Nat using (ℕ; _⊔_) renaming (_≤_ to _≤ℕ_; _*_ to _ℕ*_)
open import Data.Nat.Properties as Nat using (m≤m⊔n; m≤n⊔m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; _<_; _≤_)
open import Data.Rational.Base using (-_)
open import Data.Rational.Properties using
  (≤-trans; <⇒≤; ≤-<-trans; <-≤-trans; <-trans; +-mono-<-≤; +-comm; ≮⇒≥; <-cmp)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst; subst₂)
open import Relation.Nullary.Negation using (¬_)

open import Real.Interval using (RealI; embedℚ; δ)
open import Real.IntervalEquiv using (node; l; u; width; l-mono; u-mono)
open import Real.Interval.Arith using (0ℝ)
open import Real.Interval.Continuity using (0<embedℚ; embedℚ-mono)
open import Real.Interval.Embed using (embedℚ-*)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-sym)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Laws using (*ℝ-zeroˡ)
open import Real.Interval.Mul.Order using (u-prod-corner; u-nonNeg; δ-below)
open import Real.Interval.Node using (l-dyadic)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.Rational using (pos-diff; plus-diff)
open import Real.Interval.OrderComplete.Base using
  (Subset; Upper; Occupied; Located; _≤ℝ_)
open import Real.Interval.OrderLe using (≤ℝ-refl; <⇒≤ℝ; <-≤ℝ-trans)
open import Real.Interval.OrderLaws using (≈-<-resp; width-below-strict)
open import Real.Interval.Sqrt.Bounds using
  (sq-widen; decide-below; l-layer-≤; sq-<; sub-lt-swap
  ; sq-gap-pos)

module _ (y : RealI) (0<y : 0ℝ <ℝ y) where

  ----------------------------------------------------------------------
  -- The square-root cut
  --
  -- 平方根割

  -- For a positive real y the subset P x = (0 ≤ x) × (x * x < y) is
  -- located: for rationals p < q either some member lies above p or every
  -- member lies below q. This is the first Located instance in the
  -- repository and the only input the order-complete interface needs
  -- beyond a member and an upper bound.
  --
  -- 对正实数 y，子集 P x = (0 ≤ x) × (x * x < y) 是定位的：对有理数
  -- p < q，要么有成员高于 p，要么所有成员都低于 q。这是仓内第一个
  -- Located 实例，也是序完备接口除“一个成员 + 一个上界”之外唯一的输入。
  P : Subset
  P x = (0ℝ ≤ℝ x) × (x *ℝ x <ℝ y)

  -- Zero is a member.
  --
  -- 零是成员。
  P-0 : P 0ℝ
  P-0 = ≤ℝ-refl , ≈-<-resp (≈ℝ-sym (*ℝ-zeroˡ 0ℝ)) 0<y

  -- A negative rational is strictly below zero, hence below zeroℝ.
  --
  -- 负有理数严格低于零，故低于零ℝ。
  embed-below-zero : (p : ℚ) → p < 0ℚ → embedℚ p <ℝ 0ℝ
  embed-below-zero p p<0 = embedℚ-mono p 0ℚ p<0

  ----------------------------------------------------------------------
  -- The occupied side: a small rational above p still has square < y
  --
  -- 占据侧：略高于 p 的有理数其平方仍 < y

  occupied-below : (p : ℚ) (k : ℕ) → 0ℚ ≤ p → p * p < l y k
                 → Occupied P p
  occupied-below p k 0≤p pp<ly =
    let
      r , p<r , rr<ly = sq-widen p (l y k) 0≤p pp<ly

      0<r : 0ℚ < r
      0<r = ≤-<-trans 0≤p p<r

      0≤x : 0ℝ ≤ℝ embedℚ r
      0≤x = <⇒≤ℝ (0<embedℚ r 0<r)

      x-sq≈ : embedℚ r *ℝ embedℚ r ≈ℝ embedℚ (r * r)
      x-sq≈ = ≈ℝ-sym (embedℚ-* r r)

      rr<y : embedℚ (r * r) <ℝ y
      rr<y = <-≤ℝ-trans (embedℚ-mono (r * r) (l y k) rr<ly) (l-layer-≤ y k)

      sq<y : embedℚ r *ℝ embedℚ r <ℝ y
      sq<y = ≈-<-resp (≈ℝ-sym x-sq≈) rr<y

      p<x : embedℚ p <ℝ embedℚ r
      p<x = embedℚ-mono p r p<r
    in
      embedℚ r , (0≤x , sq<y) , p<x

  ----------------------------------------------------------------------
  -- The upper side: a member of P is below q
  --
  -- 上界侧：P 的成员低于 q

  upper-above : (p q : ℚ) (k : ℕ) → 0ℚ ≤ p → p < q
              → width y k < q * q - p * p
              → ¬ (p * p < l y k) → Upper P q
  upper-above p q k 0≤p p<q wk<gap ¬lt x (x≥0 , xx<y) =
    let
      0<q : 0ℚ < q
      0<q = ≤-<-trans 0≤p p<q

      lyk≤pp : l y k ≤ p * p
      lyk≤pp = ≮⇒≥ ¬lt

      m : ℕ
      m = proj₁ xx<y

      uxxm<lym : u (x *ℝ x) m < l y m
      uxxm<lym = proj₂ xx<y

      K : ℕ
      K = k ⊔ m

      k≤K : k ≤ℕ K
      k≤K = m≤m⊔n k m

      m≤K : m ≤ℕ K
      m≤K = m≤n⊔m k m

      ------------------------------------------------------------------
      -- l y K < q * q
      --
      -- 下端点 l y K 仍低于 q * q

      l+w≡u : l y k + width y k ≡ u y k
      l+w≡u = plus-diff (l y k) (u y k)

      lwk<pp+gap : l y k + width y k < p * p + (q * q - p * p)
      lwk<pp+gap =
        subst₂ _<_
          (+-comm (width y k) (l y k))
          (+-comm (q * q - p * p) (p * p))
          (+-mono-<-≤ wk<gap lyk≤pp)

      pp+gap≡q2 : p * p + (q * q - p * p) ≡ q * q
      pp+gap≡q2 = plus-diff (p * p) (q * q)

      uyk<q2 : u y k < q * q
      uyk<q2 =
        subst (λ z → z < q * q) l+w≡u
          (subst (λ z → l y k + width y k < z) pp+gap≡q2 lwk<pp+gap)

      lyK≤uyK : l y K ≤ u y K
      lyK≤uyK = <⇒≤ (RealI.lo (node y K))

      uyK≤uyk : u y K ≤ u y k
      uyK≤uyk = u-mono y k≤K

      lyK<q2 : l y K < q * q
      lyK<q2 = ≤-<-trans lyK≤uyK (≤-<-trans uyK≤uyk uyk<q2)

      ------------------------------------------------------------------
      -- u x (2K)² < q * q
      --
      -- 上端点平方 u x (2K)² 仍低于 q * q

      u2K²≤uxxK : u x (2 ℕ* K) * u x (2 ℕ* K) ≤ u (x *ℝ x) K
      u2K²≤uxxK = u-prod-corner x x K

      uxxK≤uxxm : u (x *ℝ x) K ≤ u (x *ℝ x) m
      uxxK≤uxxm = u-mono (x *ℝ x) m≤K

      lym≤lyK : l y m ≤ l y K
      lym≤lyK = l-mono y m≤K

      u2K²<lym : u x (2 ℕ* K) * u x (2 ℕ* K) < l y m
      u2K²<lym = ≤-<-trans (≤-trans u2K²≤uxxK uxxK≤uxxm) uxxm<lym

      u2K²<lyK : u x (2 ℕ* K) * u x (2 ℕ* K) < l y K
      u2K²<lyK = <-≤-trans u2K²<lym lym≤lyK

      0≤u2K : 0ℚ ≤ u x (2 ℕ* K)
      0≤u2K = u-nonNeg x x≥0 (2 ℕ* K)

      u2K²<q2 : u x (2 ℕ* K) * u x (2 ℕ* K) < q * q
      u2K²<q2 = <-trans u2K²<lyK lyK<q2

      ------------------------------------------------------------------
      -- Pick a layer above which x is below the rational q
      --
      -- 选取层，使 x 低于有理数 q

      gap>0 : 0ℚ < q - u x (2 ℕ* K)
      gap>0 = sq-gap-pos (u x (2 ℕ* K)) q 0≤u2K 0<q u2K²<q2

      probe : Σ ℕ (λ N → 2 ℕ* K ≤ℕ N × δ N < q - u x (2 ℕ* K))
      probe = δ-below (q - u x (2 ℕ* K)) gap>0 (2 ℕ* K)

      N : ℕ
      N = proj₁ probe

      2K≤N : 2 ℕ* K ≤ℕ N
      2K≤N = proj₁ (proj₂ probe)

      δN<gap : δ N < q - u x (2 ℕ* K)
      δN<gap = proj₂ (proj₂ probe)

      uxN≤u2K : u x N ≤ u x (2 ℕ* K)
      uxN≤u2K = u-mono x 2K≤N

      u2K<-dN+q : u x (2 ℕ* K) < - δ N + q
      u2K<-dN+q = sub-lt-swap (u x (2 ℕ* K)) (δ N) q δN<gap

      uxN<-dN+q : u x N < - δ N + q
      uxN<-dN+q = ≤-<-trans uxN≤u2K u2K<-dN+q
    in
      N , subst (λ z → u x N < z) (sym (l-dyadic q N)) uxN<-dN+q

  ----------------------------------------------------------------------
  -- Locatedness
  --
  -- 定位性

  upper-case : (p q : ℚ) → p < q → 0ℚ ≤ p → Occupied P p ⊎ Upper P q
  upper-case p q p<q 0≤p =
    let
      pp<qq : p * p < q * q
      pp<qq = sq-< p q 0≤p p<q

      gap>0 : 0ℚ < q * q - p * p
      gap>0 = pos-diff (p * p) (q * q) pp<qq

      probe : Σ ℕ (λ j → 0 ≤ℕ j × width y j < q * q - p * p)
      probe = width-below-strict y (q * q - p * p) 0 gap>0

      k : ℕ
      k = proj₁ probe

      wk<gap : width y k < q * q - p * p
      wk<gap = proj₂ (proj₂ probe)

      branch : (p * p < l y k) ⊎ (¬ (p * p < l y k))
             → Occupied P p ⊎ Upper P q
      branch =
        [ (λ lt → inj₁ (occupied-below p k 0≤p lt))
        , (λ ¬lt → inj₂ (upper-above p q k 0≤p p<q wk<gap ¬lt))
        ]
    in
      branch (decide-below y k p)

  located : Located P
  located p q p<q with <-cmp p 0ℚ
  ... | tri< p<0 _ _ = inj₁ (0ℝ , P-0 , embed-below-zero p p<0)
  ... | tri≈ ¬p<0 _ _ = upper-case p q p<q (≮⇒≥ ¬p<0)
  ... | tri> ¬p<0 _ _ = upper-case p q p<q (≮⇒≥ ¬p<0)
