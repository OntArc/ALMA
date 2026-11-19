------------------------------------------------------------------------
-- Laws of the square root that do not need the square identity
--
-- 不需要平方恒等式的平方根定律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Sqrt.Laws where

open import Data.Nat using (ℕ; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; _*_; _<_; _≤_)
open import Data.Rational.Properties as ℚP using (≤-refl; *-zeroˡ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; subst; refl; trans; cong)
open import Relation.Nullary.Negation using (¬_)

open import Real.IntervalEquiv using (l; u; l-mono; node)
open import Real.Interval using (RealI; embedℚ; δ-pos)
open import Real.Interval.Arith using (0ℝ)
open import Real.Interval.Continuity using (0<embedℚ; embedℚ-mono)
open import Real.Interval.DensityArch using (dense)
open import Real.Interval.Embed using (embedℚ-*)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-sym; ≈ℝ-trans; ≈ℝ-refl)
open import Real.Interval.Kit using (n≤2n)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Laws using (*ℝ-comm; *ℝ-zeroˡ; *ℝ-assoc)
open import Real.Interval.Mul.Cong using (*ℝ-cong)
open import Real.Interval.Mul.Order using
  (<-*mono; ≈-<-respʳ; u-prod-corner; ≤-resp-≈ʳ; l-prod-pos
  ; u-dyadic-0; *ℝ-≤-mono; ≤-resp-≈ˡ; *ℝ-nonNeg; pos*pos)
open import Real.Interval.Node using (node-*ℝ)
open import Real.Interval.Order using (_<ℝ_; <-trans; <-irrefl)
open import Real.Interval.OrderLe using
  (≤ℝ-refl; <⇒≤ℝ; <-≤ℝ-trans; ≤ℝ-<trans; ≤ℝ-antisym)
open import Real.Interval.OrderLaws using (≈-<-resp)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans; Bracket)
open import Real.Interval.OrderComplete using (br-seq; u-sup; l-sup)
open import Real.Interval.Reasoning.Equiv using (beginℝ_; _≈ℝ⟨_⟩_; _∎ℝ)
open import Real.Interval.Recip using (recipℝ)
open import Real.Interval.RecipLaws using (recipℝ-pos; recipℝ-mul; recipℝ-cong)
open import Real.Interval.Sqrt.Located using (P; P-0; located)
open import Real.Interval.Sqrt.Bounds using
  (sq-widen; embedℚ-reflect; l-layer-≤; u-layer-≤)
open import Real.Interval.Sqrt.Core using
  (sqrtℝ; sqrt-upper; sqrt-least; sqrt-nonNeg; rq; isUpper)

------------------------------------------------------------------------
-- Monotonicity
--
-- 单调性

-- Monotonicity and strict positivity follow directly from the
-- order-complete interface: every member of P y is a member of P z when
-- y ≤ z, and a small rational square below y gives a positive member.
-- The identity sqrt y * sqrt y ≈ y needs a two-sided squeeze and is left
-- to a later slice.
--
-- 单调性与严格正性直接来自序完备接口：y ≤ z 时 P y 的成员都是 P z 的
-- 成员；y 下方的小有理平方给出正成员。平方恒等式
-- sqrt y * sqrt y ≈ y 需要双向夹逼，留待后续切片。
sqrt-mono : (y z : RealI) (0y : 0ℝ <ℝ y) (0z : 0ℝ <ℝ z)
          → y ≤ℝ z → sqrtℝ y 0y ≤ℝ sqrtℝ z 0z
sqrt-mono y z 0y 0z y≤z = sqrt-least y 0y (sqrtℝ z 0z) step
  where
    step : (x : RealI) → P y 0y x → x ≤ℝ sqrtℝ z 0z
    step x (x≥0 , xx<y) =
      sqrt-upper z 0z x (x≥0 , <-≤ℝ-trans xx<y y≤z)

------------------------------------------------------------------------
-- Strict positivity
--
-- 严格正性

sqrt-pos : (y : RealI) (0y : 0ℝ <ℝ y) → 0ℝ <ℝ sqrtℝ y 0y
sqrt-pos y 0y =
  let
    probe : Σ ℚ (λ s → (0ℝ <ℝ embedℚ s) × (embedℚ s <ℝ y))
    probe = dense {x = 0ℝ} {y = y} 0y

    s : ℚ
    s = proj₁ probe

    0<es : 0ℝ <ℝ embedℚ s
    0<es = proj₁ (proj₂ probe)

    es<y : embedℚ s <ℝ y
    es<y = proj₂ (proj₂ probe)

    0<s : 0ℚ < s
    0<s = embedℚ-reflect 0ℚ s 0<es

    0*0<s : 0ℚ * 0ℚ < s
    0*0<s = subst (λ z → z < s) (sym (*-zeroˡ 0ℚ)) 0<s

    wid : Σ ℚ (λ r → 0ℚ < r × r * r < s)
    wid = sq-widen 0ℚ s (≤-refl {0ℚ}) 0*0<s

    r : ℚ
    r = proj₁ wid

    0<r : 0ℚ < r
    0<r = proj₁ (proj₂ wid)

    rr<s : r * r < s
    rr<s = proj₂ (proj₂ wid)

    x : RealI
    x = embedℚ r

    x≥0 : 0ℝ ≤ℝ x
    x≥0 = <⇒≤ℝ (0<embedℚ r 0<r)

    rr<y : embedℚ (r * r) <ℝ y
    rr<y = <-trans (embedℚ-mono (r * r) s rr<s) es<y

    xx<y : x *ℝ x <ℝ y
    xx<y = ≈-<-resp (embedℚ-* r r) rr<y

    px : P y 0y x
    px = x≥0 , xx<y

    x≤sqrt : x ≤ℝ sqrtℝ y 0y
    x≤sqrt = sqrt-upper y 0y x px

    0<x : 0ℝ <ℝ x
    0<x = 0<embedℚ r 0<r
  in
    <-≤ℝ-trans 0<x x≤sqrt

------------------------------------------------------------------------
-- Algebraic invariants of the two-sided squeeze
--
-- 双向夹逼所需的两条代数不变量

-- Squares are strictly monotone on the positives, so a point strictly
-- below a member of P has square below y, while any strict upper bound
-- of P must have square at least y: were its square below y it would
-- itself be a member of P, violating strictness at itself. These are the
-- two facts the squeeze for sqrt y * sqrt y ≈ y consumes.
--
-- 在正数上平方严格单调，故严格低于 P 的成员的点其平方低于 y；而 P 的
-- 严格上界其平方必不小于 y：若平方低于 y 它自己就成了 P 的成员，与对
-- 自身的严格性冲突。这两条正是 sqrt y * sqrt y ≈ y 的夹逼所用。
sq-lt : (a b : RealI) → 0ℝ <ℝ a → a <ℝ b → a *ℝ a <ℝ b *ℝ b
sq-lt a b 0<a a<b =
  let
    0<b : 0ℝ <ℝ b
    0<b = <-trans 0<a a<b

    aa<ba : a *ℝ a <ℝ b *ℝ a
    aa<ba = <-*mono a b a a<b 0<a

    ab<bb : a *ℝ b <ℝ b *ℝ b
    ab<bb = <-*mono a b b a<b 0<b

    aa<ab : a *ℝ a <ℝ a *ℝ b
    aa<ab = ≈-<-respʳ (≈ℝ-sym (*ℝ-comm a b)) aa<ba
  in
    <-trans aa<ab ab<bb

sq-of-member : (y : RealI) (0y : 0ℝ <ℝ y) (l x : RealI)
             → P y 0y x → l <ℝ x → 0ℝ <ℝ l
             → l *ℝ l <ℝ y
sq-of-member y 0y l x (_ , xx<y) l<x 0<l =
  <-trans (sq-lt l x 0<l l<x) xx<y

sq-of-upper : (y : RealI) (0y : 0ℝ <ℝ y) (u : RealI)
            → 0ℝ ≤ℝ u → ((x : RealI) → P y 0y x → x <ℝ u)
            → y ≤ℝ u *ℝ u
sq-of-upper y 0y u 0≤u ub uu<y = <-irrefl u (ub u (0≤u , uu<y))

------------------------------------------------------------------------
-- Embedding preserves the non-strict order
--
-- 嵌入保持非严格序

-- Reflection of the embedded strict order turns the rational bound inside
-- out: were embed q below embed p, then q < p while p ≤ q.
--
-- 嵌入严格序的反射把有理界翻出来：若 embed q 低于 embed p，则 q < p，
-- 与 p ≤ q 冲突。
embedℚ-≤ : (p q : ℚ) → p ≤ q → embedℚ p ≤ℝ embedℚ q
embedℚ-≤ p q p≤q h =
  ℚP.<-irrefl refl
    (ℚP.≤-<-trans p≤q (embedℚ-reflect q p h))

------------------------------------------------------------------------
-- Lower half of the square identity: y ≤ sqrt y * sqrt y
--
-- 平方恒等式下半：y ≤ sqrt y * sqrt y

-- The bisection brackets give, at every level, a strict upper bound b of
-- P, hence y ≤ (embed b)² by sq-of-upper. The product's upper corner
-- chains that to the layer u (sqrt * sqrt) k, and the assumed gap
-- sqrt * sqrt < y supplies the opposing layer.
--
-- 二分括号在每一层给出 P 的严格上界 b，由 sq-of-upper 得 y ≤ (embed b)²；
-- 乘积的上角把它接到 sqrt * sqrt 的第 k 层，而假设的间隙
-- sqrt * sqrt < y 给出相反方向的层。
sqrt-square-lower : (y : RealI) (0y : 0ℝ <ℝ y)
                  → y ≤ℝ sqrtℝ y 0y *ℝ sqrtℝ y 0y
sqrt-square-lower y 0y sq<y =
  let
    sq : RealI
    sq = sqrtℝ y 0y

    k : ℕ
    k = proj₁ sq<y

    hk : u (sq *ℝ sq) k < l y k
    hk = proj₂ sq<y

    n : ℕ
    n = Data.Nat._*_ 2 k

    isUp : (z : RealI) → P y 0y z → z ≤ℝ rq y 0y
    isUp = isUpper y 0y

    br : ℕ → Bracket (P y 0y)
    br = br-seq {P = P y 0y} (located y 0y) {x₀ = 0ℝ}
           (P-0 y 0y) {u₀ = rq y 0y} isUp

    b : ℚ
    b = Bracket.b (br n)

    b-ub : (z : RealI) → P y 0y z → z <ℝ embedℚ b
    b-ub = Bracket.upper (br n)

    0<eb : 0ℝ <ℝ embedℚ b
    0<eb = b-ub 0ℝ (P-0 y 0y)

    y≤eb² : y ≤ℝ embedℚ b *ℝ embedℚ b
    y≤eb² = sq-of-upper y 0y (embedℚ b) (<⇒≤ℝ 0<eb) b-ub

    y≤ebb : y ≤ℝ embedℚ (b * b)
    y≤ebb = ≤-resp-≈ʳ y≤eb² (≈ℝ-sym (embedℚ-* b b))

    ub : ℚ
    ub = u (sq *ℝ sq) k

    usq≡b : u sq n ≡ b
    usq≡b = u-sup {P = P y 0y} (located y 0y) {x₀ = 0ℝ}
              (P-0 y 0y) {u₀ = rq y 0y} isUp n

    b≤ub : b * b ≤ ub
    b≤ub = subst (λ z → z * z ≤ ub) usq≡b
             (u-prod-corner sq sq k)

    y≤eub : y ≤ℝ embedℚ ub
    y≤eub = ≤ℝ-trans y≤ebb (embedℚ-≤ (b * b) ub b≤ub)

    hkℝ : embedℚ ub <ℝ embedℚ (l y k)
    hkℝ = embedℚ-mono ub (l y k) hk

    eub<y : embedℚ ub <ℝ y
    eub<y = <-≤ℝ-trans hkℝ (l-layer-≤ y k)

    y<y : y <ℝ y
    y<y = ≤ℝ-<trans y≤eub eub<y
  in
    <-irrefl y y<y

------------------------------------------------------------------------
-- Upper half of the square identity: sqrt y * sqrt y ≤ y
--
-- 平方恒等式上半：sqrt y * sqrt y ≤ y

-- Since sqrt y is positive, some level makes its lower endpoint positive,
-- and l-prod-pos identifies the lower endpoint of the square exactly as
-- the square of that endpoint. The bracket's occupant then puts that
-- endpoint's square strictly below y, while the assumed gap would put the
-- square above it.
--
-- sqrt y 正，故某一层其下端为正；l-prod-pos 把平方的下端恰好识别成该
-- 端点的平方。括号的占有点再把该端点平方压到 y 之下，而假设的间隙要求
-- 平方在 y 之上。
sqrt-square-upper : (y : RealI) (0y : 0ℝ <ℝ y)
                  → sqrtℝ y 0y *ℝ sqrtℝ y 0y ≤ℝ y
sqrt-square-upper y 0y ys<ss =
  let
    s : RealI
    s = sqrtℝ y 0y

    isUp : (z : RealI) → P y 0y z → z ≤ℝ rq y 0y
    isUp = isUpper y 0y

    br : ℕ → Bracket (P y 0y)
    br = br-seq {P = P y 0y} (located y 0y) {x₀ = 0ℝ}
           (P-0 y 0y) {u₀ = rq y 0y} isUp

    k : ℕ
    k = proj₁ ys<ss

    hk : u y k < l (s *ℝ s) k
    hk = proj₂ ys<ss

    ps : 0ℝ <ℝ s
    ps = sqrt-pos y 0y

    k₀ : ℕ
    k₀ = proj₁ ps

    h₀ : u 0ℝ k₀ < l s k₀
    h₀ = proj₂ ps

    0<lsk₀ : 0ℚ < l s k₀
    0<lsk₀ = ℚP.<-trans (δ-pos k₀)
      (subst (λ z → z < l s k₀) (u-dyadic-0 k₀) h₀)

    K : ℕ
    K = k ⊔ k₀

    k≤K = m≤m⊔n k k₀

    k₀≤K = m≤n⊔m k k₀

    0<lsK : 0ℚ < l s K
    0<lsK = ℚP.<-≤-trans 0<lsk₀ (l-mono s k₀≤K)

    J : ℕ
    J = Data.Nat._*_ 2 K

    K≤J = n≤2n K

    0<lsJ : 0ℚ < l s J
    0<lsJ = ℚP.<-≤-trans 0<lsK (l-mono s K≤J)

    lp : l (s *ℝ s) K ≡ l s J * l s J
    lp = trans (cong RealI.l (node-*ℝ s s K))
           (l-prod-pos (node s J) (node s J) 0<lsJ 0<lsJ)

    occ : Σ RealI (λ x → P y 0y x × (embedℚ (Bracket.a (br J)) <ℝ x))
    occ = Bracket.occ (br J)

    x : RealI
    x = proj₁ occ

    px : P y 0y x
    px = proj₁ (proj₂ occ)

    a<x : embedℚ (Bracket.a (br J)) <ℝ x
    a<x = proj₂ (proj₂ occ)

    a≡lsJ : Bracket.a (br J) ≡ l s J
    a≡lsJ = sym (l-sup {P = P y 0y} (located y 0y) {x₀ = 0ℝ}
                   (P-0 y 0y) {u₀ = rq y 0y} isUp J)

    els<x : embedℚ (l s J) <ℝ x
    els<x = subst (λ q → embedℚ q <ℝ x) a≡lsJ a<x

    0<els : 0ℝ <ℝ embedℚ (l s J)
    0<els = 0<embedℚ (l s J) 0<lsJ

    els²<y : embedℚ (l s J) *ℝ embedℚ (l s J) <ℝ y
    els²<y = <-trans (sq-lt (embedℚ (l s J)) x 0<els els<x)
               (proj₂ px)

    ells<y : embedℚ (l s J * l s J) <ℝ y
    ells<y = ≈-<-resp (≈ℝ-sym (embedℚ-* (l s J) (l s J))) els²<y

    eK<y : embedℚ (l (s *ℝ s) K) <ℝ y
    eK<y = subst (λ z → embedℚ z <ℝ y) (sym lp) ells<y

    ek≤K : l (s *ℝ s) k ≤ l (s *ℝ s) K
    ek≤K = l-mono (s *ℝ s) k≤K

    ek<y : embedℚ (l (s *ℝ s) k) <ℝ y
    ek<y = ≤ℝ-<trans (embedℚ-≤ (l (s *ℝ s) k) (l (s *ℝ s) K) ek≤K)
              eK<y

    euy<y : embedℚ (u y k) <ℝ y
    euy<y = <-trans (embedℚ-mono (u y k) (l (s *ℝ s) k) hk) ek<y

    y≤euy : y ≤ℝ embedℚ (u y k)
    y≤euy = u-layer-≤ y k

    y<y : y <ℝ y
    y<y = ≤ℝ-<trans y≤euy euy<y
  in
    <-irrefl y y<y

------------------------------------------------------------------------
-- The square identity
--
-- 平方恒等式

sqrt-square : (y : RealI) (0y : 0ℝ <ℝ y)
            → sqrtℝ y 0y *ℝ sqrtℝ y 0y ≈ℝ y
sqrt-square y 0y =
  ≤ℝ-antisym (sqrt-square-upper y 0y) (sqrt-square-lower y 0y)

------------------------------------------------------------------------
-- Uniqueness of the root
--
-- 根的唯一性

-- Among non-negative solutions of s * s ≈ y the root is the only one. The
-- proof needs no decidability: non-strict order is the negation of strict
-- order, so excluding the two strict cases yields both directions at once.
--
-- 在 s * s ≈ y 的非负解中，根只有一个。证明不需要可判定性：非严格序
-- 本就是严格序的否定，故排除两个严格情形即同时得到两个方向。
sqrt-unique : (y : RealI) (0y : 0ℝ <ℝ y) (s : RealI)
            → 0ℝ ≤ℝ s → s *ℝ s ≈ℝ y
            → s ≈ℝ sqrtℝ y 0y
sqrt-unique y 0y s 0≤s ss≈y =
  let
    t : RealI
    t = sqrtℝ y 0y

    0<t : 0ℝ <ℝ t
    0<t = sqrt-pos y 0y

    tt≈y : t *ℝ t ≈ℝ y
    tt≈y = sqrt-square y 0y

    ¬s<t : ¬ (s <ℝ t)
    ¬s<t s<t =
      let
        ss≤st : s *ℝ s ≤ℝ s *ℝ t
        ss≤st = ≤-resp-≈ʳ
                  (*ℝ-≤-mono s t s (<⇒≤ℝ s<t) 0≤s)
                  (*ℝ-comm t s)

        st<tt : s *ℝ t <ℝ t *ℝ t
        st<tt = <-*mono s t t s<t 0<t

        ss<tt : s *ℝ s <ℝ t *ℝ t
        ss<tt = ≤ℝ-<trans ss≤st st<tt

        ss<y : s *ℝ s <ℝ y
        ss<y = ≈-<-respʳ tt≈y ss<tt

        y<y : y <ℝ y
        y<y = ≈-<-resp ss≈y ss<y
      in
        <-irrefl y y<y

    ¬t<s : ¬ (t <ℝ s)
    ¬t<s t<s =
      let
        tt<st : t *ℝ t <ℝ s *ℝ t
        tt<st = <-*mono t s t t<s 0<t

        st≤ss : s *ℝ t ≤ℝ s *ℝ s
        st≤ss = ≤-resp-≈ˡ (*ℝ-comm t s)
                  (*ℝ-≤-mono t s s (<⇒≤ℝ t<s) 0≤s)

        tt<ss : t *ℝ t <ℝ s *ℝ s
        tt<ss = <-≤ℝ-trans tt<st st≤ss

        tt<y : t *ℝ t <ℝ y
        tt<y = ≈-<-respʳ ss≈y tt<ss

        y<y : y <ℝ y
        y<y = ≈-<-resp tt≈y tt<y
      in
        <-irrefl y y<y

    s≤t : s ≤ℝ t
    s≤t = ¬t<s

    t≤s : t ≤ℝ s
    t≤s = ¬s<t
  in
    ≤ℝ-antisym s≤t t≤s

------------------------------------------------------------------------
-- The root of a product
--
-- 乘积的根

-- The root is multiplicative on positive factors. Once uniqueness is
-- available the work is pure rearrangement: four factors, two applications
-- of the square identity, and associativity and commutativity in between.
-- Note that positivity of the product is an explicit argument rather than
-- a pos*pos call inside the statement: sqrtℝ consumes a proof of 0ℝ <ℝ y,
-- and a statement that fixes that proof term would force every caller to
-- write the very same term (real-order proofs are not automatically
-- irrelevant). Making it explicit keeps the lemma usable with whatever
-- proof the caller owns.
--
-- 根在正因子之间可乘。有了唯一性以后剩下的只是重排：四个因子、两次
-- 平方式，中间用结合律与交换律。
-- 注意乘积为正作为显式参数，而不是在陈述内直接 pos*pos：sqrtℝ 要吃一个
-- 0ℝ <ℝ y 的证明，若陈述把该证明项写死，调用方就必须写出同一个项（实数
-- 序证明并不自动满足无关性）。做成显式参数后，调用方持有哪个证明都能用。
sqrt-of-mul : (y z : RealI) (0y : 0ℝ <ℝ y) (0z : 0ℝ <ℝ z)
              (0yz : 0ℝ <ℝ y *ℝ z)
            → sqrtℝ (y *ℝ z) 0yz
            ≈ℝ sqrtℝ y 0y *ℝ sqrtℝ z 0z
sqrt-of-mul y z 0y 0z 0yz =
  let
    s : RealI
    s = sqrtℝ y 0y

    t : RealI
    t = sqrtℝ z 0z

    0st : 0ℝ ≤ℝ s *ℝ t
    0st = *ℝ-nonNeg s t (sqrt-nonNeg y 0y) (sqrt-nonNeg z 0z)

    square : (s *ℝ t) *ℝ (s *ℝ t) ≈ℝ y *ℝ z
    square =
      beginℝ
        (s *ℝ t) *ℝ (s *ℝ t)
          ≈ℝ⟨ *ℝ-assoc s t (s *ℝ t) ⟩
        s *ℝ (t *ℝ (s *ℝ t))
          ≈ℝ⟨ *ℝ-cong ≈ℝ-refl (≈ℝ-sym (*ℝ-assoc t s t)) ⟩
        s *ℝ ((t *ℝ s) *ℝ t)
          ≈ℝ⟨ *ℝ-cong ≈ℝ-refl (*ℝ-cong (*ℝ-comm t s) ≈ℝ-refl) ⟩
        s *ℝ ((s *ℝ t) *ℝ t)
          ≈ℝ⟨ *ℝ-cong ≈ℝ-refl (*ℝ-assoc s t t) ⟩
        s *ℝ (s *ℝ (t *ℝ t))
          ≈ℝ⟨ ≈ℝ-sym (*ℝ-assoc s s (t *ℝ t)) ⟩
        (s *ℝ s) *ℝ (t *ℝ t)
          ≈ℝ⟨ *ℝ-cong (sqrt-square y 0y) (sqrt-square z 0z) ⟩
        y *ℝ z
      ∎ℝ

    eq : s *ℝ t ≈ℝ sqrtℝ (y *ℝ z) 0yz
    eq = sqrt-unique (y *ℝ z) 0yz (s *ℝ t) 0st square
  in
    ≈ℝ-sym eq

------------------------------------------------------------------------
-- The root of a reciprocal
--
-- 倒数的根

-- Roots commute with reciprocals on positive inputs. Again only
-- uniqueness is needed: the reciprocal of the root squares to the
-- reciprocal of the base, because reciprocal is multiplicative
-- (recipℝ-mul) and the square identity rewrites the base.
-- As with sqrt-of-mul the three positivity proofs are explicit arguments
-- rather than terms spelled out in the statement, for the same reason:
-- sqrtℝ and recipℝ consume proofs, and fixing them by term would restrict
-- callers to that exact proof.
--
-- 根在正输入上与倒数可交换。仍然只需要唯一性：根的倒数平方后是底数的
-- 倒数，因为倒数是乘性的（recipℝ-mul），而平方式再把底数换回来。
-- 与 sqrt-of-mul 一样，三个正性证明作为显式参数，理由相同：sqrtℝ 与
-- recipℝ 都要吃证明，把证明项写死会限制调用方。
sqrt-of-inv : (y : RealI) (0y : 0ℝ <ℝ y)
              (0iy : 0ℝ <ℝ recipℝ y 0y) (0t : 0ℝ <ℝ sqrtℝ y 0y)
            → sqrtℝ (recipℝ y 0y) 0iy ≈ℝ recipℝ (sqrtℝ y 0y) 0t
sqrt-of-inv y 0y 0iy 0t =
  let
    t : RealI
    t = sqrtℝ y 0y

    r : RealI
    r = recipℝ t 0t

    0r : 0ℝ ≤ℝ r
    0r = <⇒≤ℝ (recipℝ-pos t 0t)

    0tt : 0ℝ <ℝ t *ℝ t
    0tt = pos*pos t t 0t 0t

    square : r *ℝ r ≈ℝ recipℝ y 0y
    square =
      ≈ℝ-trans
        (≈ℝ-sym (recipℝ-mul t t 0t 0t))
        (recipℝ-cong (t *ℝ t) y 0tt 0y (sqrt-square y 0y))

    eq : r ≈ℝ sqrtℝ (recipℝ y 0y) 0iy
    eq = sqrt-unique (recipℝ y 0y) 0iy r 0r square
  in
    ≈ℝ-sym eq

------------------------------------------------------------------------
-- The identity at zero
--
-- 零处的恒等式

-- sqrtℝ only accepts a strictly positive input, so the value at zero is
-- stated at the level of the specification instead: the radical of a base
-- equal to zero is zero, non-negative, and squares back to the base.
--
-- sqrtℝ 只接受严格正输入，故零处的取值在规格层面陈述：等于零的底数其
-- 根为零、非负，且平方回到该底数。
sqrt-of-zero : (y : RealI) → y ≈ℝ 0ℝ →
  (0ℝ ≤ℝ 0ℝ) × (0ℝ *ℝ 0ℝ ≈ℝ y)
sqrt-of-zero y y≈0 =
  ≤ℝ-refl , ≈ℝ-trans (*ℝ-zeroˡ 0ℝ) (≈ℝ-sym y≈0)
