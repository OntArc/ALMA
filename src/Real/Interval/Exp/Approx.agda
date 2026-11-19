------------------------------------------------------------------------
-- The exponential series and its positivity
--
-- 指数级数与其正性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Approx where

open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_; _-_; ∣_∣)
  renaming (-_ to neg)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; <⇒≤; <-≤-trans; <-trans; <-asym; +-mono-≤; +-mono-≤-<
  ; +-monoˡ-<; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ; +-assoc
  ; +-monoˡ-≤; +-monoʳ-≤; neg-antimono-≤)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Real using (ε; CauchySeq; half)
open import Real.CauchyToInterval using
  (cauchy→realI; point; centre-point; centre-cauchy→realI; M; K; K≥k; μ≤M)
open import Real.IntervalEquiv using (centre; l; u)
open import Real.Interval using (δ; δ-pos; δ-half)
open import Real.Interval.Arith using (0ℝ)
open import Real.Interval.Complete using (_⟶_)
open import Real.Interval.ContinuityRecipBasic using
  (l-cauchy→realI; u-cauchy→realI)
open import Real.Interval.Embed using (δ0≡half)
open import Real.Interval.Exp.Core as ExpCore using
  (term; term-nonNeg; expPartial; expPartial-cauchy; expSeq; expq
  ; expPartial-nonNeg; expPartial-suc; _≤ℕ_)
open import Real.Interval.Kit using (abs-swap; half+half≡1)
open import Real.Interval.LimitLaws using (ε-mono; abs<⇒lower)
open import Real.Interval.Node using (l-dyadic; u-dyadic)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)

------------------------------------------------------------------------
-- The partial sums converge to expq q as rational points
--
-- 部分和作为有理点收敛于 expq q

-- Core built expq : (q : ℚ) → 0 ≤ q → RealI as the completion of the
-- rational partial sums, and deliberately stopped there. The laws are
-- collected in this module, and they are all proved the same way: the
-- approximating sequence
--     approx q = λ n → point (expPartial q n)
-- of *rational points* is shown to converge to expq q, and then every
-- property is established for that sequence of points and transferred to
-- expq q by uniqueness of limits. This is why the module exists at all:
-- an argument repeated at the level of the interval construction would
-- have to fight the width of the nested brackets each time, while at the
-- level of points the same argument is a statement about rational partial
-- sums, which Core already controls.
-- Slice 1 (this section) is the bridge itself: expq-approx.
--     approx q = λ n → point (expPartial q n)
-- The k-th centre of expq q is the sampled partial sum at index M k, and
-- the k-th centre of point c is exactly c, so the distance to be bounded
-- is between two partial sums: one at n, one at M k. The Cauchy modulus
-- of Core at precision K k handles both, because M k ≥ μ (K k), and
-- ε (K k) ≤ ε k since K k ≥ k.
--
-- Core 把 expq : (q : ℚ) → 0 ≤ q → RealI 构造成有理部分和的完备化，并且
-- 有意停在那里。定律集中在本模块，且都用同一种方式证明：先把逼近序列
-- （全是有理点）证到收敛于 expq q，此后每条性质都在这个点序列上证出，
-- 再借极限唯一性搬到 expq q 上。这正是本模块存在的理由：在区间构造层
-- 重复论证，每次都要和嵌套区间宽度纠缠；而在点序列层，同一论证只是关于
-- 有理部分和的陈述，而后者已由 Core 控制。
-- 第 1 片（本节）就是这个桥：expq-approx。
-- expq q 的第 k 层中心是下标 M k 处的采样部分和，而 point c 的第 k 层
-- 中心恰为 c，故要界的距离是两个部分和之差：一个在 n，一个在 M k。
-- Core 在精度 K k 处的柯西模同时覆盖两者，因为 M k ≥ μ (K k)，且由
-- K k ≥ k 得 ε (K k) ≤ ε k。
expq-approx : (q : ℚ) (0≤q : 0ℚ ≤ q)
            → (λ n → point (expPartial q n)) ⟶ expq q 0≤q
expq-approx q 0≤q k =
  let μK : ℕ
      μK = proj₁ (expPartial-cauchy q 0≤q (K k))
      bound = proj₂ (expPartial-cauchy q 0≤q (K k))
      Mk : ℕ
      Mk = M (expSeq q 0≤q) k
      μK≤Mk : μK ≤ℕ Mk
      μK≤Mk = μ≤M (expSeq q 0≤q) k
  in μK , (λ n n≥ →
       let h : ∣ expPartial q n - expPartial q Mk ∣ < ε (K k)
           h = bound n Mk n≥ μK≤Mk
           eL : centre (point (expPartial q n)) k ≡ expPartial q n
           eL = centre-point (expPartial q n) k
           eR : centre (expq q 0≤q) k ≡ expPartial q Mk
           eR = centre-cauchy→realI (expSeq q 0≤q) k
           absEq : ∣ centre (point (expPartial q n)) k - centre (expq q 0≤q) k ∣
                 ≡ ∣ expPartial q n - expPartial q Mk ∣
           absEq = cong ∣_∣ (cong₂ (λ p r → p - r) eL eR)
       in subst (λ z → z < ε k) (sym absEq)
                  (<-≤-trans h (ε-mono (K≥k k))))

------------------------------------------------------------------------
-- The real exponential is non-negative
--
-- 实指数非负

-- Non-negativity is a statement about endpoints, so it does not need the
-- point-sequence bridge: the argument is a direct computation at one
-- level. If expq q were strictly below 0ℝ, some level n would have
--     u (expq q) n < l 0ℝ n.
-- The upper endpoint is the sampled partial sum plus δ n, and l 0ℝ n is
-- neg (δ n) + 0, so that inequality says a + δ n < neg (δ n) for a
-- partial sum a that is non-negative. But a + δ n is already positive
-- (0 ≤ a and 0 < δ n), while a + δ n < neg (δ n) forces 0 < neg (δ n)
-- and hence δ n < 0, contradicting 0 < δ n.
--
-- 非负性是端点层的陈述，不需要点序列桥：论证是在某一层上的直接计算。
-- 若 expq q 严格小于 0ℝ，则存在某层 n 使
--     u (expq q) n < l 0ℝ n。
-- 上端点是采样部分和加 δ n，而 l 0ℝ n 是 neg (δ n) + 0，故该不等式即
-- a + δ n < neg (δ n)，其中部分和 a 非负。但 a + δ n 本身为正
-- （0 ≤ a 且 0 < δ n），而 a + δ n < neg (δ n) 逼迫 0 < neg (δ n)，
-- 进而 δ n < 0，与 0 < δ n 矛盾。
expq-nonNeg : (q : ℚ) (0≤q : 0ℚ ≤ q) → 0ℝ ≤ℝ expq q 0≤q
expq-nonNeg q 0≤q (n , w) =
  let a : ℚ
      a = expPartial q (M (expSeq q 0≤q) n)
      uEq : u (expq q 0≤q) n ≡ a + δ n
      uEq = u-cauchy→realI (expSeq q 0≤q) n
      lEq : l 0ℝ n ≡ neg (δ n) + 0ℚ
      lEq = l-dyadic 0ℚ n
      w1 : a + δ n < l 0ℝ n
      w1 = subst (λ z → z < l 0ℝ n) uEq w
      w2 : a + δ n < neg (δ n) + 0ℚ
      w2 = subst (λ z → a + δ n < z) lEq w1
      step : 0ℚ + 0ℚ < a + δ n
      step = +-mono-≤-< (expPartial-nonNeg q 0≤q (M (expSeq q 0≤q) n)) (δ-pos n)
      pos-ad : 0ℚ < a + δ n
      pos-ad = subst (λ z → z < a + δ n) (+-identityˡ 0ℚ) step
      pos-negδ : 0ℚ < neg (δ n)
      pos-negδ =
        subst (λ z → 0ℚ < z) (+-identityʳ (neg (δ n)))
          (<-trans pos-ad w2)
      shifted : 0ℚ + δ n < neg (δ n) + δ n
      shifted = +-monoˡ-< (δ n) pos-negδ
      delta-lt-0 : δ n < 0ℚ
      delta-lt-0 =
        subst (λ z → z < 0ℚ) (+-identityˡ (δ n))
          (subst (λ z → 0ℚ + δ n < z) (+-inverseˡ (δ n)) shifted)
  in <-asym (δ-pos n) delta-lt-0

------------------------------------------------------------------------
-- The real exponential is strictly positive
--
-- 实指数严格为正

-- This slice deliberately avoids Core's sampling index M and instead
-- reuses the approximation bridge of slice 1: expq-approx states that
-- point (expPartial q n) converges to expq q. At level k = 2 we obtain
-- an N such that |centre x 2 - expPartial q n| < ε 2 for n ≥ N. Taking
-- n = suc N gives expPartial q (suc N) ≥ 1 (expPartial-suc-ge), hence
-- expPartial q (suc N) - ε 2 < centre x 2, i.e. 1 - ε 2 ≤ centre x 2
-- (eps2≤half and oneMinusHalf push 1 - ε 2 above half). On the other
-- side δ 2 + δ 2 ≡ δ 1 < half (δ-half 1, delta1<half), so
-- δ 2 + δ 2 < centre x 2 and the level-2 endpoint comparison closes:
-- δ 2 + 0 < centre x 2 + neg (δ 2).
-- Two reasons for the bridge rather than M: first, expPartial q 0 = 0
-- while expPartial q 1 = 1, so the partial sums are not even Cauchy at
-- n = 0; sampling through M would force a proof that the Cauchy index N
-- is at least 1, i.e. a with-abstraction over the whole Σ of
-- expPartial-cauchy. Second, the bridge's bound already has the shape
-- abs<⇒lower wants: a distance between a point value and the centre.
--
-- 这一片不走 Core 的采样指标 M，而是走第 1 片已经证好的逼近桥：
-- expq-approx 说 point (expPartial q n) 收敛到 expq q。取层 k = 2，
-- 得到某个 N 使 n ≥ N 时 |centre x 2 - expPartial q n| < ε 2。再取
-- n = suc N，则 expPartial q (suc N) ≥ 1（expPartial-suc-ge），于是
-- expPartial q (suc N) - ε 2 < centre x 2，也就是
-- 1 - ε 2 ≤ centre x 2（eps2≤half 与 oneMinusHalf 把 1 - ε 2 压到
-- half 以上）。另一侧 δ 2 + δ 2 ≡ δ 1 < half（δ-half 1、delta1<half），
-- 于是 δ 2 + δ 2 < centre x 2，第 2 层的端点比较随之收口：
-- δ 2 + 0 < centre x 2 + neg (δ 2)。
-- 走逼近桥而不是走 M 的理由有两个：一是 expPartial q 0 = 0 而
-- expPartial q 1 = 1，部分和在 n = 0 处根本不 Cauchy，若按 M 采样，
-- 就得先证 Cauchy 指标 N ≥ 1（那要对 expPartial-cauchy 的 Σ 做
-- with-抽象，展开整条 Cauchy 证明项）；二是逼近桥的界本来就是
-- 「点序列与极限中心之差 < ε k」，正好是 abs<⇒lower 需要的形状。
expPartial-suc-ge : (q : ℚ) (0≤q : 0ℚ ≤ q) (m : ℕ)
                  → 1ℚ ≤ expPartial q (suc m)
expPartial-suc-ge q 0≤q zero =
  subst (λ z → 1ℚ ≤ z) (+-identityˡ 1ℚ) (≤-refl {1ℚ})
expPartial-suc-ge q 0≤q (suc m) =
  let step = +-mono-≤ (expPartial-suc-ge q 0≤q m) (term-nonNeg q 0≤q (suc m))
      step' = subst (λ z → z ≤ expPartial q (suc m) + term q (suc m))
                    (+-identityʳ 1ℚ) step
  in subst (λ z → 1ℚ ≤ z) (sym (expPartial-suc q (suc m))) step'

expPartial-ge-one : (q : ℚ) (0≤q : 0ℚ ≤ q) (m : ℕ) → 1 ≤ℕ m
                  → 1ℚ ≤ expPartial q m
expPartial-ge-one q 0≤q zero ()
expPartial-ge-one q 0≤q (suc m) _ = expPartial-suc-ge q 0≤q m

-- δ 1 is strictly below half: δ 1 + δ 1 ≡ δ 0 ≡ half and δ 1 > 0.
--
-- δ 1 严格小于 half：δ 1 + δ 1 ≡ δ 0 ≡ half，且 δ 1 > 0。
delta1<half : δ 1 < half
delta1<half =
  let step : 0ℚ + δ 1 < δ 1 + δ 1
      step = +-monoˡ-< (δ 1) (δ-pos 1)
      step' : δ 1 < δ 1 + δ 1
      step' = subst (λ z → z < δ 1 + δ 1) (+-identityˡ (δ 1)) step
      twoDelta : δ 1 + δ 1 ≡ half
      twoDelta = trans (δ-half 0) δ0≡half
  in subst (λ z → δ 1 < z) twoDelta step'

-- half ≤ 1 - ε 2, since ε 2 ≤ ε 1 ≡ half and 1 - half ≡ half.
--
-- half ≤ 1 - ε 2：因 ε 2 ≤ ε 1 ≡ half，且 1 - half ≡ half。
eps2≤half : ε 2 ≤ half
eps2≤half = ε-mono {1} {2} (s≤s z≤n)

oneMinusHalf : 1ℚ + neg half ≡ half
oneMinusHalf =
  trans (cong (_+ neg half) (sym half+half≡1))
    (trans (+-assoc half half (neg half))
           (trans (cong (half +_) (+-inverseʳ half)) (+-identityʳ half)))

half≤one-minus-ε2 : half ≤ 1ℚ - ε 2
half≤one-minus-ε2 =
  let add1 : 1ℚ + neg half ≤ 1ℚ + neg (ε 2)
      add1 = +-monoʳ-≤ 1ℚ (neg-antimono-≤ eps2≤half)
  in subst (λ z → z ≤ 1ℚ + neg (ε 2)) (sym oneMinusHalf) add1

expq-pos : (q : ℚ) (0≤q : 0ℚ ≤ q) → 0ℝ <ℝ expq q 0≤q
expq-pos q 0≤q =
  let cs = expSeq q 0≤q
      x = cauchy→realI cs
      N = proj₁ (expq-approx q 0≤q 2)
      h = proj₂ (expq-approx q 0≤q 2)
      a : ℚ
      a = expPartial q (suc N)
      h0 : ∣ centre (point a) 2 - centre x 2 ∣ < ε 2
      h0 = h (suc N) (NatP.n≤1+n N)
      h1 : ∣ a - centre x 2 ∣ < ε 2
      h1 = subst₂ (λ p q → ∣ p - q ∣ < ε 2) (centre-point a 2) refl h0
      h1' : ∣ centre x 2 - a ∣ < ε 2
      h1' = subst (λ z → z < ε 2) (abs-swap a (centre x 2)) h1
      low : a - ε 2 < centre x 2
      low = abs<⇒lower h1'
      one≤a : 1ℚ ≤ a
      one≤a = expPartial-ge-one q 0≤q (suc N) (s≤s z≤n)
      ε2≤a : 1ℚ - ε 2 ≤ a - ε 2
      ε2≤a = +-monoˡ-≤ (neg (ε 2)) one≤a
      twoDelta : δ 2 + δ 2 ≡ δ 1
      twoDelta = δ-half 1
      deltaLtHalf : δ 2 + δ 2 < half
      deltaLtHalf = subst (λ z → z < half) twoDelta delta1<half
      c = CauchySeq.f cs (M cs 2)
      ceq : centre x 2 ≡ c
      ceq = centre-cauchy→realI cs 2
      deltaLtCentre : δ 2 + δ 2 < centre x 2
      deltaLtCentre = <-≤-trans deltaLtHalf
                        (≤-trans half≤one-minus-ε2 (≤-trans ε2≤a (<⇒≤ low)))
      deltaLt : δ 2 + δ 2 < c
      deltaLt = subst (λ z → δ 2 + δ 2 < z) ceq deltaLtCentre
      shifted : (δ 2 + δ 2) + neg (δ 2) < c + neg (δ 2)
      shifted = +-monoˡ-< (neg (δ 2)) deltaLt
      cancel : (δ 2 + δ 2) + neg (δ 2) ≡ δ 2 + 0ℚ
      cancel = trans (+-assoc (δ 2) (δ 2) (neg (δ 2)))
                   (cong (δ 2 +_) (+-inverseʳ (δ 2)))
      w : δ 2 + 0ℚ < c + neg (δ 2)
      w = subst (λ z → z < c + neg (δ 2)) cancel shifted
      uEq : u 0ℝ 2 ≡ δ 2 + 0ℚ
      uEq = u-dyadic 0ℚ 2
      lEq : l x 2 ≡ c + neg (δ 2)
      lEq = l-cauchy→realI cs 2
  in 2 , subst (λ y → u 0ℝ 2 < y) lEq
             (subst (λ x' → x' < l x 2) uEq w)
