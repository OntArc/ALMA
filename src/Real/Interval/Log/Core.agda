------------------------------------------------------------------------
-- The logarithm as a supremum
--
-- 对数作为上确界
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Log.Core where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _<_; _≤_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; <⇒≤; <-≤-trans; <-trans; <-asym; +-monoʳ-<; +-monoˡ-≤; <-cmp
  ; +-comm; +-assoc; +-identityˡ; +-identityʳ; +-inverseʳ; neg-antimono-<; ≮⇒≥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (¬_)

open import Real using (embed; 0<embed; 0<ε; ε; _≈_)
open import Real.CauchyToInterval using (M)
open import Real.IntervalEquiv using (l; u)
open import Real.Interval using (RealI; embedℚ; δ; δ-pos)
open import Real.Interval.Arith using (1ℝ)
open import Real.Interval.Continuity using (embedℚ-mono)
open import Real.Interval.DensityArch using (archimedean)
open import Base.RationalRing using (0<1)
open import Real.Interval.Exp.Core using (expPartial; expSeq; expq)
open import Real.Interval.Exp.Order using (expq-zero; expq-mono; expq-strict-mono)
open import Real.Interval.Exp.Step using (expq-u; expq-step-up; M-lower)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-sym; ≈ℝ-refl)
open import Real.Interval.Mul.Order using (≈-<-respʳ)
open import Real.Interval.Node using (l-dyadic; u-dyadic)
open import Real.Interval.Order as Ord using (_<ℝ_; <-cotrans)
open import Real.Interval.OrderLe using
  (<-≤ℝ-trans; ≤ℝ-<trans; ≤ℝ-resp-≈; ≈⇒≤ℝ∧)
open import Real.Interval.OrderLaws using (≈-<-resp)
open import Real.Interval.OrderComplete.Base using
  (Subset; Upper; Occupied; Located; _≤ℝ_)
open import Real.Interval.OrderComplete using (sup; sup-upper; sup-least)
open import Real.Interval.RetractCauchy using (cauchy→realI-cong)

------------------------------------------------------------------------
-- expq does not depend on the proof of non-negativity
--
-- expq 不依赖非负性的证明

-- For y with 1 < y, log y is the least upper bound of the located set
--     P x = Σ ℚ (λ q → (0 ≤ q) × (x ≈ embedℚ q) × (expq q < y))
-- of rational points whose exponential is still below y. Membership is
-- witnessed by embedℚ 0 and expq 0 ≈ 1 < y. The upper bound is the
-- image embedℚ m of a natural number m with y < m: a member with
-- r ≥ m would give embedℚ m ≤ embedℚ r ≤ expq r < y < embedℚ m.
--     P x = Σ ℚ (λ q → (0 ≤ q) × (x ≈ embedℚ q) × (expq q < y))
-- The sequence part is literally the same function; only the modulus
-- differs, so the two Cauchy sequences are metrically equivalent.
-- These lemmas do not mention the base, so they live outside the
-- parameterised module below.
--
-- 对满足 1 < y 的 y，log y 是定位集
-- 的上确界：成员是那些指数仍在 y 以下的有理点。成员由 embedℚ 0 与
-- expq 0 ≈ 1 < y 给出。上界取自然数 m（满足 y < m）的像 embedℚ m：
-- 若有成员满足 r ≥ m，则 embedℚ m ≤ embedℚ r ≤ expq r < y < embedℚ m
-- 矛盾。
-- 序列部分就是同一个函数，只有模数不同，故两条柯西列度量等价。
-- 这些引理与底数无关，因此放在下面带参数的模块之外。
expSeq-irrel : (q : ℚ) (p p' : 0ℚ ≤ q) → expSeq q p ≈ expSeq q p'
expSeq-irrel q p p' k = 0 , λ n _ →
  let c : expPartial q n + neg (expPartial q n) < ε k
      c = subst (λ z → z < ε k) (sym (+-inverseʳ (expPartial q n))) (0<ε k)
  in c , c

expq-irrel : (q : ℚ) (p p' : 0ℚ ≤ q) → expq q p ≈ℝ expq q p'
expq-irrel q p p' = cauchy→realI-cong (expSeq-irrel q p p')

-- Monotonicity at arbitrary proofs of non-negativity.
--
-- 任意非负性证明下的单调性。
expq-mono-any : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q)
              → p ≤ q → expq p 0≤p ≤ℝ expq q 0≤q
expq-mono-any p q 0≤p 0≤q p≤q =
  ≤ℝ-resp-≈ ≈ℝ-refl (expq-irrel q (≤-trans 0≤p p≤q) 0≤q)
    (expq-mono p q 0≤p p≤q)

expq-strict-any : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q)
                → p < q → expq p 0≤p <ℝ expq q 0≤q
expq-strict-any p q 0≤p 0≤q p<q =
  let step : expq p 0≤p <ℝ expq q (≤-trans 0≤p (<⇒≤ p<q))
      step = expq-strict-mono p q 0≤p p<q
      le : expq q (≤-trans 0≤p (<⇒≤ p<q)) ≤ℝ expq q 0≤q
      le = proj₁ (≈⇒≤ℝ∧ (expq-irrel q (≤-trans 0≤p (<⇒≤ p<q)) 0≤q))
  in <-≤ℝ-trans step le

module _ (y : RealI) (1<y : 1ℝ <ℝ y) where

  ----------------------------------------------------------------------
  -- The logarithm cut
  --
  -- 对数割

  P : Subset
  P x = Σ ℚ (λ q → Σ (0ℚ ≤ q) (λ 0≤q → (x ≈ℝ embedℚ q) × (expq q 0≤q <ℝ y)))

  -- Zero is a member: 0 ≈ embedℚ 0 and expq 0 ≈ 1 < y.
  --
  -- 零是成员：0 ≈ embedℚ 0 且 expq 0 ≈ 1 < y。
  P-0 : P (embedℚ 0ℚ)
  P-0 = 0ℚ , (≤-refl , (≈ℝ-refl , ≈-<-resp (≈ℝ-sym expq-zero) 1<y))

  -- A negative rational is strictly below zero.
  --
  -- 负有理数严格低于零。
  embed-below-zero : (p : ℚ) → p < 0ℚ → embedℚ p <ℝ embedℚ 0ℚ
  embed-below-zero p p<0 = embedℚ-mono p 0ℚ p<0

  -- If q ≤ r fails then r < q.
  --
  -- 若 q ≤ r 不成立，则 r < q。
  not-≤⇒< : (r q : ℚ) → ¬ (q ≤ r) → r < q
  not-≤⇒< r q nle with <-cmp r q
  ... | tri< lt _ _ = lt
  ... | tri≈ _ eq _ = ⊥-elim (nle (subst (λ z → q ≤ z) (sym eq) ≤-refl))
  ... | tri> _ _ q<r = ⊥-elim (nle (<⇒≤ q<r))

  ----------------------------------------------------------------------
  -- Arithmetic helpers
  --
  -- 算术辅助

  0<1ℚ : 0ℚ < 1ℚ
  0<1ℚ = 0<1

  neg-δ<0 : (k : ℕ) → neg (δ k) < 0ℚ
  neg-δ<0 k = neg-antimono-< {0ℚ} {δ k} (δ-pos k)

  m<1+m : (m : ℚ) → m < 1ℚ + m
  m<1+m m =
    subst₂ _<_
      (trans (+-comm m 0ℚ) (+-identityˡ m))
      (+-comm m 1ℚ)
      (+-monoʳ-< m 0<1ℚ)

  m<δ+m : (k : ℕ) (m : ℚ) → m < δ k + m
  m<δ+m k m =
    subst₂ _<_
      (+-identityʳ m)
      (+-comm m (δ k))
      (+-monoʳ-< m (δ-pos k))

  neg-δ+m<m : (k : ℕ) (m : ℚ) → neg (δ k) + m < m
  neg-δ+m<m k m =
    subst₂ _<_
      (+-comm m (neg (δ k)))
      (+-identityʳ m)
      (+-monoʳ-< m (neg-δ<0 k))

  -- (e + (δ + δ)) + neg δ ≡ e + δ.
  --
  -- (e + (δ + δ)) + neg δ ≡ e + δ。
  δ-triple : (e : ℚ) (k : ℕ)
           → (e + (δ k + δ k)) + neg (δ k) ≡ e + δ k
  δ-triple e k =
    trans (+-assoc e (δ k + δ k) (neg (δ k)))
      (trans (cong (e +_) cancel) refl)
    where
    cancel : (δ k + δ k) + neg (δ k) ≡ δ k
    cancel = trans (+-assoc (δ k) (δ k) (neg (δ k)))
               (trans (cong (δ k +_) (+-inverseʳ (δ k)))
                      (+-identityʳ (δ k)))

  ----------------------------------------------------------------------
  -- embedℚ m ≤ expq m: linear growth read at the level of layers
  --
  -- embedℚ m ≤ expq m：逐层的线性增长

  embed≤exp : (m : ℚ) (0≤m : 0ℚ ≤ m) → embedℚ m ≤ℝ expq m 0≤m
  embed≤exp m 0≤m (k , h) =
    let
      Mk : ℕ
      Mk = M (expSeq m 0≤m) k

      lower : 1ℚ + m ≤ expPartial m Mk + (δ k + δ k)
      lower = M-lower m 0≤m k

      add-negδ : (1ℚ + m) + neg (δ k)
               ≤ (expPartial m Mk + (δ k + δ k)) + neg (δ k)
      add-negδ = +-monoˡ-≤ (neg (δ k)) lower

      lower' : (1ℚ + m) + neg (δ k) ≤ expPartial m Mk + δ k
      lower' = subst (λ z → (1ℚ + m) + neg (δ k) ≤ z)
                 (δ-triple (expPartial m Mk) k) add-negδ

      strict : neg (δ k) + m < (1ℚ + m) + neg (δ k)
      strict = subst (λ z → neg (δ k) + m < z)
                 (+-comm (neg (δ k)) (1ℚ + m))
                 (+-monoʳ-< (neg (δ k)) (m<1+m m))

      gt : neg (δ k) + m < expPartial m Mk + δ k
      gt = <-≤-trans strict lower'

      uP≡ : u (expq m 0≤m) k ≡ expPartial m Mk + δ k
      uP≡ = expq-u m 0≤m k

      lE : l (embedℚ m) k ≡ neg (δ k) + m
      lE = l-dyadic m k

      lt : l (embedℚ m) k < u (expq m 0≤m) k
      lt = subst (λ z → z < u (expq m 0≤m) k) (sym lE)
             (subst (λ z → neg (δ k) + m < z) (sym uP≡) gt)
    in
      <-asym lt h

  ----------------------------------------------------------------------
  -- The occupied side: a member strictly above p
  --
  -- 占据侧：严格高于 p 的成员

  occupied-up : (p : ℚ) (0≤p : 0ℚ ≤ p) (k₀ : ℕ)
              → u (expq p 0≤p) k₀ < l y k₀ → Occupied P p
  occupied-up p 0≤p k₀ hlt =
    let
      st = expq-step-up p 0≤p y k₀ hlt
      h = proj₁ st
      0<h = proj₁ (proj₂ st)
      0≤ph = proj₁ (proj₂ (proj₂ st))
      k₂ = proj₁ (proj₂ (proj₂ (proj₂ st)))
      hlt₂ = proj₂ (proj₂ (proj₂ (proj₂ st)))

      p<ph : p < p + h
      p<ph = subst₂ _<_
               (+-identityʳ p)
               refl
               (+-monoʳ-< p 0<h)

      x : RealI
      x = embedℚ (p + h)

      member : P x
      member = p + h , (0≤ph , (≈ℝ-refl , (k₂ , hlt₂)))
    in
      x , (member , embedℚ-mono p (p + h) p<ph)

  ----------------------------------------------------------------------
  -- The upper side: every member is below q
  --
  -- 上界侧：每个成员都低于 q

  upper-above : (q : ℚ) (0≤q : 0ℚ ≤ q) (y<eq : y <ℝ expq q 0≤q) → Upper P q
  upper-above q 0≤q y<eq x (r , (0≤r , (x≈ , er<y))) =
    let
      not-q≤r : ¬ (q ≤ r)
      not-q≤r q≤r =
        let mono : expq q 0≤q ≤ℝ expq r 0≤r
            mono = expq-mono-any q r 0≤q 0≤r q≤r
            eq<y : expq q 0≤q <ℝ y
            eq<y = ≤ℝ-<trans mono er<y
        in Ord.<-irrefl (expq q 0≤q) (Ord.<-trans eq<y y<eq)

      r<q : r < q
      r<q = not-≤⇒< r q not-q≤r
    in
      ≈-<-resp (≈ℝ-sym x≈) (embedℚ-mono r q r<q)

  ----------------------------------------------------------------------
  -- Locatedness: <-cotrans splits expq p < expq q against y
  --
  -- 定位性：<-cotrans 把 expq p < expq q 对 y 切开

  decide : (p q : ℚ) → p < q → 0ℚ ≤ p → Occupied P p ⊎ Upper P q
  decide p q p<q 0≤p =
    let
      0≤q : 0ℚ ≤ q
      0≤q = ≤-trans 0≤p (<⇒≤ p<q)

      mono : expq p 0≤p <ℝ expq q 0≤q
      mono = expq-strict-mono p q 0≤p p<q

      br : (expq p 0≤p <ℝ y) ⊎ (y <ℝ expq q 0≤q)
      br = <-cotrans {x = expq p 0≤p} {y = y} {z = expq q 0≤q} mono
    in
      [ (λ lt → inj₁ (occupied-up p 0≤p (proj₁ lt) (proj₂ lt)))
      , (λ gt → inj₂ (upper-above q 0≤q gt))
      ] br

  located : Located P
  located p q p<q with <-cmp p 0ℚ
  ... | tri< p<0 _ _ = inj₁ (embedℚ 0ℚ , (P-0 , embed-below-zero p p<0))
  ... | tri≈ ¬p<0 _ _ = decide p q p<q (≮⇒≥ ¬p<0)
  ... | tri> ¬p<0 _ _ = decide p q p<q (≮⇒≥ ¬p<0)

  ----------------------------------------------------------------------
  -- A rational bound above y, and its image
  --
  -- 高于 y 的有理界及其像

  n : ℕ
  n = proj₁ (archimedean y)

  m : ℚ
  m = embed n

  y<m : y <ℝ embedℚ m
  y<m = proj₂ (archimedean y)

  0≤m : 0ℚ ≤ m
  0≤m with n
  ... | zero = ≤-refl
  ... | suc j = <⇒≤ (0<embed j)

  ----------------------------------------------------------------------
  -- embedℚ m is an upper bound for P
  --
  -- embedℚ m 是 P 的上界

  isUpper : (x : RealI) → P x → x ≤ℝ embedℚ m
  isUpper x (r , (0≤r , (x≈ , er<y))) h =
    let
      em<er : embedℚ m <ℝ embedℚ r
      em<er = ≈-<-respʳ x≈ h

      k : ℕ
      k = proj₁ em<er

      hlt : u (embedℚ m) k < l (embedℚ r) k
      hlt = proj₂ em<er

      s1 : m < u (embedℚ m) k
      s1 = subst (λ z → m < z) (sym (u-dyadic m k)) (m<δ+m k m)

      s2 : u (embedℚ m) k < r
      s2 = <-trans (subst (λ z → u (embedℚ m) k < z) (l-dyadic r k) hlt)
             (neg-δ+m<m k r)

      m<r : m < r
      m<r = <-trans s1 s2

      em<exp : embedℚ m <ℝ expq r 0≤r
      em<exp = <-≤ℝ-trans (embedℚ-mono m r m<r) (embed≤exp r 0≤r)

      exp<em : expq r 0≤r <ℝ embedℚ m
      exp<em = Ord.<-trans er<y y<m
    in
      Ord.<-irrefl (embedℚ m) (Ord.<-trans em<exp exp<em)

  ----------------------------------------------------------------------
  -- The logarithm
  --
  -- 对数

  logℝ : RealI
  logℝ = sup {P = P} located {x₀ = embedℚ 0ℚ} P-0 {u₀ = embedℚ m} isUpper

  log-upper : (x : RealI) → P x → x ≤ℝ logℝ
  log-upper = sup-upper {P = P} located {x₀ = embedℚ 0ℚ} P-0
                {u₀ = embedℚ m} isUpper

  log-least : (u₀ : RealI) → ((x : RealI) → P x → x ≤ℝ u₀)
            → logℝ ≤ℝ u₀
  log-least = sup-least {P = P} located {x₀ = embedℚ 0ℚ} P-0
                {u₀ = embedℚ m} isUpper

  ----------------------------------------------------------------------
  -- Rational points below the logarithm are members
  --
  -- 对数下方的有理点是成员

  log-member : (q : ℚ) (0≤q : 0ℚ ≤ q) → expq q 0≤q <ℝ y
             → P (embedℚ q)
  log-member q 0≤q q<y = q , (0≤q , (≈ℝ-refl , q<y))
