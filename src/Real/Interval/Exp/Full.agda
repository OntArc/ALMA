------------------------------------------------------------------------
-- The total exponential at the rational level
--
-- 有理层的全指数
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Full where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; _≤_; _<_; _+_; -_)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; <⇒≤; neg-antimono-≤; neg-antimono-<; <-cmp
  ; <-irrefl; ≤-<-trans; <-asym; +-inverseʳ)
open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using
 (_≡_; refl; sym; cong; subst)
open import Relation.Nullary using (¬_)

open import Base.RationalRing using (neg-involutive; neg-0)
open import Real using (_≈_; ≈-refl; ε; 0<ε)
open import Real.Interval using (RealI)
open import Real.Interval.Arith using (0ℝ; 1ℝ)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Exp.Core using (expPartial; expSeq; expq)
open import Real.Interval.Exp.Approx using (expq-pos)
open import Real.Interval.Exp.Order using (expq-zero; expq-mono; expq-strict-mono)
open import Real.Interval.Kit using (neg-of-nonpos)
open import Real.Interval.Order using (_<ℝ_; <-trans)
open import Real.Interval.OrderLe using (<-≤ℝ-trans; <⇒≤ℝ; ≤ℝ-refl)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.OrderLaws using (≈-<-resp)
open import Real.Interval.Mul.Order using (≤-resp-≈ˡ; ≤-resp-≈ʳ; ≈-<-respʳ)
open import Real.Interval.Recip using (recipℝ)
open import Real.Interval.RecipLaws using (recipℝ-pos; recipℝ-cong)
open import Real.Interval.RecipOrder using
  (recipℝ-antitone; recipℝ-≤-1-of; recipℝ-pos-irr; recipℝ-strict-antitone-of
  ; recipℝ-lt-one-of)
open import Real.Interval.RetractCauchy using (cauchy→realI-cong)

------------------------------------------------------------------------
-- Independence of the bound proof, at the sequence level
--
-- 界的证据无关性，在序列层

-- expSeq does not depend on the proof of 0 <= q. The sequence part f is
-- literally the same function of n in both cases, and the Cauchy-level
-- closeness _≈_ compares f at the same index, so it is reflexive there:
-- the two records differ only in their modulus field, which no side of
-- the comparison looks at.
--
-- expSeq 不依赖 0 <= q 的证据：两种情形下序列部分 f 是同一个 n 的函数，
-- 而柯西层的 _≈_ 在同一指标处比较 f，故在序列层取自反性即可——两个 record
-- 只有模数字段不同，而比较的两侧都不看模数。
expSeq-irr : (q : ℚ) (p p' : 0ℚ ≤ q) → expSeq q p ≈ expSeq q p'
expSeq-irr q p p' = ≈-refl {x = expSeq q p}

-- Hence expq is independent of the bound as well.
--
-- 于是 expq 也与该界无关。
expq-irr : (q : ℚ) (p p' : 0ℚ ≤ q) → expq q p ≈ℝ expq q p'
expq-irr q p p' =
  cauchy→realI-cong {x = expSeq q p} {y = expSeq q p'} (expSeq-irr q p p')

------------------------------------------------------------------------
-- The negative branch
--
-- 负分支

-- The exponential at a non-positive rational, as the reciprocal of expq
-- at its negation. exp q = 1 / exp (-q)
-- Negating a non-positive rational gives a non-negative one; this is
-- Kit's neg-of-nonpos, used here rather than reproved.
--
-- 非正有理点处的指数，取其相反数的 expq 的倒数：exp q = 1 / exp (-q)
-- 非正有理数取负后非负；这就是 Kit 的 neg-of-nonpos，这里直接使用，不重证。
expq-neg : (q : ℚ) → q ≤ 0ℚ → RealI
expq-neg q q≤0 =
  recipℝ (expq (- q) (neg-of-nonpos {x = q} q≤0))
         (expq-pos (- q) (neg-of-nonpos {x = q} q≤0))

expq-neg-pos : (q : ℚ) (q≤0 : q ≤ 0ℚ) → 0ℝ <ℝ expq-neg q q≤0
expq-neg-pos q q≤0 =
  recipℝ-pos (expq (- q) (neg-of-nonpos {x = q} q≤0))
             (expq-pos (- q) (neg-of-nonpos {x = q} q≤0))

------------------------------------------------------------------------
-- Totality
--
-- 全定义

-- The trichotomy of q against zero picks the branch. It is passed as an
-- argument so that the selection is a case on Tri, not a with clause.
--
-- 以 q 与零的三分法选择分支。三分法作为参数传入，于是分支选择是对 Tri
-- 分情况，而不是 with 子句。
expq-branch : (q : ℚ) → Tri (0ℚ < q) (0ℚ ≡ q) (q < 0ℚ) → RealI
expq-branch q (tri< lt _ _) = expq q (<⇒≤ lt)
expq-branch q (tri≈ _ eq _) = expq q (≤-reflexive eq)
expq-branch q (tri> _ _ gt) = expq-neg q (<⇒≤ gt)

expq-total : (q : ℚ) → RealI
expq-total q = expq-branch q (<-cmp 0ℚ q)

-- On the non-negative side it agrees with Core's expq.
--
-- 非负一侧与 Core 的 expq 一致。
expq-total-nonNeg-branch : (q : ℚ) (0≤q : 0ℚ ≤ q)
                         → (t : Tri (0ℚ < q) (0ℚ ≡ q) (q < 0ℚ))
                         → expq-branch q t ≈ℝ expq q 0≤q
expq-total-nonNeg-branch q 0≤q (tri< lt _ _) = expq-irr q (<⇒≤ lt) 0≤q
expq-total-nonNeg-branch q 0≤q (tri≈ _ eq _) = expq-irr q (≤-reflexive eq) 0≤q
expq-total-nonNeg-branch q 0≤q (tri> _ _ gt) =
  ⊥-elim (<-irrefl refl (≤-<-trans 0≤q gt))

expq-total-nonNeg : (q : ℚ) (0≤q : 0ℚ ≤ q) → expq-total q ≈ℝ expq q 0≤q
expq-total-nonNeg q 0≤q = expq-total-nonNeg-branch q 0≤q (<-cmp 0ℚ q)

-- The exponential is everywhere positive.
--
-- 指数处处为正。
expq-total-pos-branch : (q : ℚ) → (t : Tri (0ℚ < q) (0ℚ ≡ q) (q < 0ℚ))
                      → 0ℝ <ℝ expq-branch q t
expq-total-pos-branch q (tri< lt _ _) = expq-pos q (<⇒≤ lt)
expq-total-pos-branch q (tri≈ _ eq _) = expq-pos q (≤-reflexive eq)
expq-total-pos-branch q (tri> _ _ gt) = expq-neg-pos q (<⇒≤ gt)

expq-total-pos : (q : ℚ) → 0ℝ <ℝ expq-total q
expq-total-pos q = expq-total-pos-branch q (<-cmp 0ℚ q)

-- exp 0 = 1.
--
-- 指数在零点等于一。
expq-total-zero : expq-total 0ℚ ≈ℝ 1ℝ
expq-total-zero =
  ≈ℝ-trans {x = expq-total 0ℚ} {y = expq 0ℚ (≤-refl {0ℚ})} {z = 1ℝ}
    (expq-total-nonNeg 0ℚ (≤-refl {0ℚ}))
    expq-zero

------------------------------------------------------------------------
-- Agreement with the two branches at a variable point
--
-- 变量点处与两个分支的一致

-- Above zero the total exponent is Core's expq at that point. This is
-- expq-total-nonNeg read at the strict bound, so no case split is needed.
--
-- 在零点以上，全指数就是该点上 Core 的 expq：把 expq-total-nonNeg 用在严格界上，
-- 无需再分情况。
expq-total-pos-branch-eq : (q : ℚ) (0<q : 0ℚ < q)
                         → expq-total q ≈ℝ expq q (<⇒≤ 0<q)
expq-total-pos-branch-eq q 0<q = expq-total-nonNeg q (<⇒≤ 0<q)

-- Below zero the total exponent is expq-neg at the same point. Both sides
-- are the reciprocal of expq at -q, so the two values differ only in which
-- bound proofs sit inside them; expq-irr removes that difference and
-- recipℝ-cong carries it through the reciprocal.
--
-- 在零点以下，全指数就是该点的 expq-neg。两边都是 -q 处 expq 的倒数，
-- 差别只在于值里装的是哪两个界证据；expq-irr 消掉这个差别，
-- recipℝ-cong 再把它抬过倒数。
expq-total-neg-branch : (q : ℚ) (q<0 : q < 0ℚ)
                      → (t : Tri (0ℚ < q) (0ℚ ≡ q) (q < 0ℚ))
                      → expq-branch q t ≈ℝ expq-neg q (<⇒≤ q<0)
expq-total-neg-branch q q<0 (tri< lt _ _) = ⊥-elim (<-asym lt q<0)
expq-total-neg-branch q q<0 (tri≈ _ eq _) =
  ⊥-elim (<-irrefl refl (subst (λ z → z < 0ℚ) (sym eq) q<0))
expq-total-neg-branch q q<0 (tri> _ _ gt) =
  recipℝ-cong (expq (- q) (neg-of-nonpos {x = q} (<⇒≤ gt)))
              (expq (- q) (neg-of-nonpos {x = q} (<⇒≤ q<0)))
              (expq-pos (- q) (neg-of-nonpos {x = q} (<⇒≤ gt)))
              (expq-pos (- q) (neg-of-nonpos {x = q} (<⇒≤ q<0)))
              (expq-irr (- q) (neg-of-nonpos {x = q} (<⇒≤ gt))
                              (neg-of-nonpos {x = q} (<⇒≤ q<0)))

-- The same statement with the trichotomy left implicit, in the shape in
-- which downstream modules use it.
--
-- 同一结论的另一种写法：三分法隐去，正是下游模块使用的形状。
expq-total-neg : (q : ℚ) (q<0 : q < 0ℚ)
               → expq-total q ≈ℝ expq-neg q (<⇒≤ q<0)
expq-total-neg q q<0 = expq-total-neg-branch q q<0 (<-cmp 0ℚ q)

-- At a non-positive point the value is, by definition, the reciprocal of
-- expq at -q; this records the unfolding so downstream modules need not
-- repeat the definition
-- The total exponent is assembled from three formulas that each carry a
-- bound proof inside the term, so every comparison below is built from
-- transports along expq-irr (for expq) and recipℝ-pos-irr (for the
-- reciprocal), with a final transport along expq-total-nonNeg.
--
-- 在非正点处，值按定义就是 -q 处 expq 的倒数；这里把这个展开记下来，
-- 下游模块不必重复定义
-- 全指数由三段都把界证据装在项里的公式拼成，故下面每次比较都由沿
-- expq-irr（对 expq）与 recipℝ-pos-irr（对倒数）的搬运拼出，
-- 最后再沿 expq-total-nonNeg 搬运一次。
expq-neg-recip : (q : ℚ) (q≤0 : q ≤ 0ℚ)
  → expq-neg q q≤0
    ≈ℝ recipℝ (expq (- q) (neg-of-nonpos {x = q} q≤0))
               (expq-pos (- q) (neg-of-nonpos {x = q} q≤0))
expq-neg-recip q q≤0 = ≈ℝ-refl

-- Transport of an expq comparison in the bound proof of its right
-- argument.
--
-- 指数比较沿右变元的界证据搬运。
expq-≤-respʳ : (a b : ℚ) (Pa : 0ℚ ≤ a) (Pb Pb' : 0ℚ ≤ b)
             → expq a Pa ≤ℝ expq b Pb → expq a Pa ≤ℝ expq b Pb'
expq-≤-respʳ a b Pa Pb Pb' i =
  ≤-resp-≈ʳ {x = expq a Pa} {y = expq b Pb} {z = expq b Pb'}
    i (expq-irr b Pb Pb')

-- The exponential at a non-negative point is at least one.
--
-- 非负点上的指数不小于一。
expq-ge-one : (q : ℚ) (0≤q : 0ℚ ≤ q) → 1ℝ ≤ℝ expq q 0≤q
expq-ge-one q 0≤q =
  ≤-resp-≈ʳ {x = 1ℝ} {y = expq q (≤-trans (≤-refl {0ℚ}) 0≤q)}
    {z = expq q 0≤q}
    (≤-resp-≈ˡ {x = expq 0ℚ (≤-refl {0ℚ})} {y = 1ℝ}
      {z = expq q (≤-trans (≤-refl {0ℚ}) 0≤q)}
      expq-zero
      (expq-mono 0ℚ q (≤-refl {0ℚ}) 0≤q))
    (expq-irr q (≤-trans (≤-refl {0ℚ}) 0≤q) 0≤q)

expq-total-ge-one : (q : ℚ) (0≤q : 0ℚ ≤ q) → 1ℝ ≤ℝ expq-total q
expq-total-ge-one q 0≤q =
  ≤-resp-≈ʳ {x = 1ℝ} {y = expq q 0≤q} {z = expq-total q}
    (expq-ge-one q 0≤q) (≈ℝ-sym (expq-total-nonNeg q 0≤q))

-- The reciprocal of the exponential at a non-negative point is at most
-- one.
--
-- 非负点处指数的倒数不大于一。
expq-inv-le-one : (q : ℚ) (P : 0ℚ ≤ - q)
                → recipℝ (expq (- q) P) (expq-pos (- q) P) ≤ℝ 1ℝ
expq-inv-le-one q P =
  recipℝ-≤-1-of (expq (- q) P) (expq-pos (- q) P) (expq-ge-one (- q) P)

expq-neg-le-one : (q : ℚ) (q≤0 : q ≤ 0ℚ) → expq-neg q q≤0 ≤ℝ 1ℝ
expq-neg-le-one q q≤0 =
  ≤-resp-≈ˡ {x = recipℝ (expq (- q) (neg-of-nonpos {x = q} q≤0))
                     (expq-pos (- q) (neg-of-nonpos {x = q} q≤0))}
    {y = expq-neg q q≤0} {z = 1ℝ}
    (≈ℝ-sym (expq-neg-recip q q≤0))
    (expq-inv-le-one q (neg-of-nonpos {x = q} q≤0))

-- Strictly below zero the total exponent is at most one.
--
-- 严格小于零时全指数不大于一。
expq-total-le-one-strict : (q : ℚ) (q<0 : q < 0ℚ) → expq-total q ≤ℝ 1ℝ
expq-total-le-one-strict q q<0 =
  ≤-resp-≈ˡ {x = expq-neg q (<⇒≤ q<0)} {y = expq-total q} {z = 1ℝ}
    (≈ℝ-sym (expq-total-neg q q<0)) (expq-neg-le-one q (<⇒≤ q<0))

expq-total-zero-le-one : expq-total 0ℚ ≤ℝ 1ℝ
expq-total-zero-le-one =
  ≤-resp-≈ˡ {x = 1ℝ} {y = expq-total 0ℚ} {z = 1ℝ}
    (≈ℝ-sym expq-total-zero) (≤ℝ-refl {x = 1ℝ})

expq-total-le-one-zero : (q : ℚ) (0≡q : 0ℚ ≡ q) → expq-total q ≤ℝ 1ℝ
expq-total-le-one-zero q 0≡q =
  ≤-resp-≈ˡ {x = expq-total 0ℚ} {y = expq-total q} {z = 1ℝ}
    (≈ℝ-sym (subst (λ z → expq-total z ≈ℝ expq-total 0ℚ) 0≡q ≈ℝ-refl))
    expq-total-zero-le-one

expq-total-le-one-branch : (q : ℚ) (q≤0 : q ≤ 0ℚ)
                           (t : Tri (0ℚ < q) (0ℚ ≡ q) (q < 0ℚ))
                         → expq-total q ≤ℝ 1ℝ
expq-total-le-one-branch q q≤0 (tri< 0<q _ _) =
  ⊥-elim (<-irrefl refl (≤-<-trans q≤0 0<q))
expq-total-le-one-branch q q≤0 (tri≈ _ 0≡q _) = expq-total-le-one-zero q 0≡q
expq-total-le-one-branch q q≤0 (tri> _ _ q<0) = expq-total-le-one-strict q q<0

-- At or below zero the total exponent is at most one.
--
-- 零点及以下，全指数不大于一。
expq-total-le-one : (q : ℚ) (q≤0 : q ≤ 0ℚ) → expq-total q ≤ℝ 1ℝ
expq-total-le-one q q≤0 = expq-total-le-one-branch q q≤0 (<-cmp 0ℚ q)

-- Monotonicity on the non-negative side.
--
-- 非负一侧的单调性。
expq-total-nonNeg-mono : (p q : ℚ) (0≤p : 0ℚ ≤ p) (p≤q : p ≤ q)
                       → expq-total p ≤ℝ expq-total q
expq-total-nonNeg-mono p q 0≤p p≤q =
  ≤-resp-≈ˡ {x = expq p 0≤p} {y = expq-total p} {z = expq-total q}
    (≈ℝ-sym (expq-total-nonNeg p 0≤p))
    (≤-resp-≈ʳ {x = expq p 0≤p} {y = expq q (≤-trans 0≤p p≤q)}
      {z = expq-total q}
      (expq-mono p q 0≤p p≤q)
      (≈ℝ-sym (expq-total-nonNeg q (≤-trans 0≤p p≤q))))

-- Below zero the total exponent is the reciprocal of the exponential at
-- -q, in one term.
--
-- 零点以下，全指数就是 -q 处指数的倒数，写成一项。
expq-total-as-inv : (q : ℚ) (q<0 : q < 0ℚ)
  → expq-total q
    ≈ℝ recipℝ (expq (- q) (neg-of-nonpos {x = q} (<⇒≤ q<0)))
              (expq-pos (- q) (neg-of-nonpos {x = q} (<⇒≤ q<0)))
expq-total-as-inv q q<0 =
  ≈ℝ-trans (expq-total-neg q q<0) (expq-neg-recip q (<⇒≤ q<0))

------------------------------------------------------------------------
-- Congruence in the point
--
-- 点的同余

-- expPartial is a plain function of the point: the bound lives only in
-- expq's own construction, not in the partial sums. Equal points therefore
-- give pointwise equal partial sums, and at equal values the symmetric
-- closeness is just 0 < ε k, which holds at every precision. So expq
-- respects equality of the point.
--
-- expPartial 是点的纯函数：界只存在于 expq 自身的构造里，不在部分和里
-- 相等的点因此给出逐点相等的部分和；在同值处对称接近就是 0 < ε k，各精度层
-- 都成立。所以 expq 尊重点的相等。
expPartial-cong : (p q : ℚ) → p ≡ q → (n : ℕ) → expPartial p n ≡ expPartial q n
expPartial-cong p q p≡q n = cong (λ z → expPartial z n) p≡q

expSeq-cong : (p q : ℚ) (p≡q : p ≡ q) (P : 0ℚ ≤ p) (Q : 0ℚ ≤ q)
            → expSeq p P ≈ expSeq q Q
expSeq-cong p q p≡q P Q k =
  0 , λ n _ →
    let
      base : expPartial p n + (- expPartial p n) < ε k
      base = subst (λ z → z < ε k) (sym (+-inverseʳ (expPartial p n))) (0<ε k)

      eq : expPartial p n ≡ expPartial q n
      eq = expPartial-cong p q p≡q n

      lower : expPartial p n + (- expPartial q n) < ε k
      lower = subst (λ z → expPartial p n + (- z) < ε k) eq base

      upper : expPartial q n + (- expPartial p n) < ε k
      upper = subst (λ z → z + (- expPartial p n) < ε k) eq base
    in
      lower , upper

expq-cong : (p q : ℚ) (p≡q : p ≡ q) (P : 0ℚ ≤ p) (Q : 0ℚ ≤ q)
          → expq p P ≈ℝ expq q Q
expq-cong p q p≡q P Q = cauchy→realI-cong (expSeq-cong p q p≡q P Q)

------------------------------------------------------------------------
-- The total exponent at a negated point
--
-- 取负点处的全指数

-- A positive input sits at a negative point after negation, and there the
-- total exponent is the reciprocal of the positive value at the input.
--
-- 正输入取负后落在负点，而该点的全指数就是输入处正值的倒数。
neg-of-pos : (q : ℚ) → 0ℚ < q → - q < 0ℚ
neg-of-pos q 0<q = subst (λ z → - q < z) neg-0 (neg-antimono-< 0<q)

expq-total-neg-pos : (q : ℚ) (0<q : 0ℚ < q)
                   → expq-total (- q)
                     ≈ℝ recipℝ (expq q (<⇒≤ 0<q)) (expq-pos q (<⇒≤ 0<q))
expq-total-neg-pos q 0<q =
  let
    h : - q < 0ℚ
    h = neg-of-pos q 0<q

    P₁ : 0ℚ ≤ - (- q)
    P₁ = neg-of-nonpos {x = - q} (<⇒≤ h)

    as-inv : expq-total (- q)
             ≈ℝ recipℝ (expq (- (- q)) P₁) (expq-pos (- (- q)) P₁)
    as-inv = expq-total-as-inv (- q) h

    pt : expq (- (- q)) P₁ ≈ℝ expq q (<⇒≤ 0<q)
    pt = expq-cong (- (- q)) q (neg-involutive q) P₁ (<⇒≤ 0<q)

    inv-eq : recipℝ (expq (- (- q)) P₁) (expq-pos (- (- q)) P₁)
           ≈ℝ recipℝ (expq q (<⇒≤ 0<q)) (expq-pos q (<⇒≤ 0<q))
    inv-eq =
      recipℝ-cong (expq (- (- q)) P₁) (expq q (<⇒≤ 0<q))
                  (expq-pos (- (- q)) P₁) (expq-pos q (<⇒≤ 0<q)) pt
  in
    ≈ℝ-trans as-inv inv-eq

-- The reciprocal reverses the comparison of the two positive
-- exponentials.
--
-- 倒数把这两个正指数的比较方向反转。
expq-inv-antitone : (p q : ℚ) (Pp : 0ℚ ≤ - p) (Qq : 0ℚ ≤ - q)
                    (m : expq (- q) Qq ≤ℝ expq (- p) Pp)
                  → recipℝ (expq (- p) Pp) (expq-pos (- p) Pp)
                    ≤ℝ recipℝ (expq (- q) Qq) (expq-pos (- q) Qq)
expq-inv-antitone p q Pp Qq m =
  ≤-resp-≈ˡ {x = recipℝ (expq (- p) Pp) (<-≤ℝ-trans (expq-pos (- q) Qq) m)}
    {y = recipℝ (expq (- p) Pp) (expq-pos (- p) Pp)}
    {z = recipℝ (expq (- q) Qq) (expq-pos (- q) Qq)}
    (recipℝ-pos-irr (expq (- p) Pp) (<-≤ℝ-trans (expq-pos (- q) Qq) m) (expq-pos (- p) Pp))
    (recipℝ-antitone (expq (- q) Qq) (expq (- p) Pp) (expq-pos (- q) Qq) m)

expq-total-nonPos-mono-core : (p q : ℚ)
    (Pp : 0ℚ ≤ - p) (Qq : 0ℚ ≤ - q)
    (ep : expq-total p ≈ℝ recipℝ (expq (- p) Pp) (expq-pos (- p) Pp))
    (eq : expq-total q ≈ℝ recipℝ (expq (- q) Qq) (expq-pos (- q) Qq))
    (m : expq (- q) Qq ≤ℝ expq (- p) Pp)
  → expq-total p ≤ℝ expq-total q
expq-total-nonPos-mono-core p q Pp Qq ep eq m =
  ≤-resp-≈ˡ {x = recipℝ (expq (- p) Pp) (expq-pos (- p) Pp)}
    {y = expq-total p} {z = expq-total q}
    (≈ℝ-sym ep)
    (≤-resp-≈ʳ {x = recipℝ (expq (- p) Pp) (expq-pos (- p) Pp)}
      {y = recipℝ (expq (- q) Qq) (expq-pos (- q) Qq)} {z = expq-total q}
      (expq-inv-antitone p q Pp Qq m) (≈ℝ-sym eq))

-- Monotonicity on the negative side.
--
-- 负一侧的单调性。
expq-total-nonPos-mono : (p q : ℚ) (p<0 : p < 0ℚ) (q<0 : q < 0ℚ)
                         (p≤q : p ≤ q)
                       → expq-total p ≤ℝ expq-total q
expq-total-nonPos-mono p q p<0 q<0 p≤q =
  expq-total-nonPos-mono-core p q
    (neg-of-nonpos {x = p} (<⇒≤ p<0))
    (neg-of-nonpos {x = q} (<⇒≤ q<0))
    (expq-total-as-inv p p<0)
    (expq-total-as-inv q q<0)
    (expq-≤-respʳ (- q) (- p) (neg-of-nonpos {x = q} (<⇒≤ q<0))
      (≤-trans (neg-of-nonpos {x = q} (<⇒≤ q<0)) (neg-antimono-≤ p≤q))
      (neg-of-nonpos {x = p} (<⇒≤ p<0))
      (expq-mono (- q) (- p) (neg-of-nonpos {x = q} (<⇒≤ q<0))
        (neg-antimono-≤ p≤q)))

-- A point at or below zero against a point at or above zero.
--
-- 零点及以下与零点及以上之间的比较。
expq-total-straddle : (p q : ℚ) (p≤0 : p ≤ 0ℚ) (0≤q : 0ℚ ≤ q)
                    → expq-total p ≤ℝ expq-total q
expq-total-straddle p q p≤0 0≤q =
  ≤ℝ-trans (expq-total-le-one p p≤0) (expq-total-ge-one q 0≤q)

-- Branch on the sign of the right argument, given a negative left
-- argument.
--
-- 已知左变元为负时，按右变元的符号选分支。
expq-total-mono-nonPos : (p q : ℚ) (p<0 : p < 0ℚ) (p≤q : p ≤ q)
                         (t : Tri (0ℚ < q) (0ℚ ≡ q) (q < 0ℚ))
                       → expq-total p ≤ℝ expq-total q
expq-total-mono-nonPos p q p<0 p≤q (tri< 0<q _ _) =
  expq-total-straddle p q (<⇒≤ p<0) (<⇒≤ 0<q)
expq-total-mono-nonPos p q p<0 p≤q (tri≈ _ 0≡q _) =
  expq-total-straddle p q (<⇒≤ p<0) (≤-reflexive 0≡q)
expq-total-mono-nonPos p q p<0 p≤q (tri> _ _ q<0) =
  expq-total-nonPos-mono p q p<0 q<0 p≤q

-- Branch on the sign of the left argument.
--
-- 按左变元的符号选分支。
expq-total-mono-sign : (p q : ℚ) (p≤q : p ≤ q)
                     (t : Tri (0ℚ < p) (0ℚ ≡ p) (p < 0ℚ))
                   → expq-total p ≤ℝ expq-total q
expq-total-mono-sign p q p≤q (tri< 0<p _ _) =
  expq-total-nonNeg-mono p q (<⇒≤ 0<p) p≤q
expq-total-mono-sign p q p≤q (tri≈ _ 0≡p _) =
  expq-total-nonNeg-mono p q (≤-reflexive 0≡p) p≤q
expq-total-mono-sign p q p≤q (tri> _ _ p<0) =
  expq-total-mono-nonPos p q p<0 p≤q (<-cmp 0ℚ q)

-- The total exponential is monotone on the whole rational line.
--
-- 全指数在整个有理直线上单调。
expq-total-mono : (p q : ℚ) → p ≤ q → expq-total p ≤ℝ expq-total q
expq-total-mono p q p≤q = expq-total-mono-sign p q p≤q (<-cmp 0ℚ p)

------------------------------------------------------------------------
-- The total exponential never vanishes
--
-- 全指数永不为零

-- expq-total-pos already gives a strict witness below every rational point;
-- reading it through the defining order turns the hypothesis expq-total q
-- ≈ 0 into the self-comparison 0 < 0, which ≤ℝ-refl refutes.
--
-- expq-total-pos 已在每个有理点给出严格见证；沿定义序搬运该见证，就把假设
-- expq-total q ≈ 0 变成 0 < 0 的自比较，再由 ≤ℝ-refl 否证。
expq-total-nonzero : (q : ℚ) → ¬ (expq-total q ≈ℝ 0ℝ)
expq-total-nonzero q q≈0 = ≤ℝ-refl (≈-<-respʳ q≈0 (expq-total-pos q))

------------------------------------------------------------------------
-- Strict monotonicity on the whole rational line
--
-- 全有理直线上的严格单调性

-- Below zero the total exponent is below one
-- Strictness is built, never refuted: each side of a rational point is
-- settled by multiplying an already strict comparison by a positive
-- factor, so every step produces a layer witness instead of deriving it
-- from a negation.
--
-- 零点以下全指数小于一
-- 严格性只靠构造给出，从不靠反证：有理点的两侧都通过把已有的严格比较
-- 乘以正因子来定，每一步都直接产出层见证，而不是从否定中导出。
expq-total-lt-one : (p : ℚ) (p<0 : p < 0ℚ) → expq-total p <ℝ 1ℝ
expq-total-lt-one p p<0 =
  let
    Pp : 0ℚ ≤ - p
    Pp = neg-of-nonpos {x = p} (<⇒≤ p<0)

    0<Pp : 0ℚ < - p
    0<Pp = neg-antimono-< {x = p} {y = 0ℚ} p<0

    0<eP : 0ℝ <ℝ expq (- p) Pp
    0<eP = expq-pos (- p) Pp

    bnd : 0ℚ ≤ - p
    bnd = ≤-trans (≤-refl {0ℚ}) (<⇒≤ 0<Pp)

    step : expq 0ℚ (≤-refl {0ℚ}) <ℝ expq (- p) bnd
    step = expq-strict-mono 0ℚ (- p) (≤-refl {0ℚ}) 0<Pp

    1<eP : 1ℝ <ℝ expq (- p) Pp
    1<eP = ≈-<-resp expq-zero (≈-<-respʳ (expq-irr (- p) bnd Pp) step)

    recip<1 : recipℝ (expq (- p) Pp) 0<eP <ℝ 1ℝ
    recip<1 = recipℝ-lt-one-of (expq (- p) Pp) 0<eP 1<eP
  in
    ≈-<-resp (≈ℝ-sym (expq-total-as-inv p p<0)) recip<1

-- Above zero the total exponent is above one.
--
-- 零点以上全指数大于一。
expq-total-gt-one : (q : ℚ) (0<q : 0ℚ < q) → 1ℝ <ℝ expq-total q
expq-total-gt-one q 0<q =
  let
    bnd : 0ℚ ≤ q
    bnd = ≤-trans (≤-refl {0ℚ}) (<⇒≤ 0<q)

    step : expq 0ℚ (≤-refl {0ℚ}) <ℝ expq q bnd
    step = expq-strict-mono 0ℚ q (≤-refl {0ℚ}) 0<q

    eP : expq q bnd ≈ℝ expq-total q
    eP = ≈ℝ-trans (expq-irr q bnd (<⇒≤ 0<q)) (≈ℝ-sym (expq-total-nonNeg q (<⇒≤ 0<q)))
  in
    ≈-<-respʳ eP (≈-<-resp expq-zero step)

-- Both ends non-negative.
--
-- 两端都非负。
expq-total-strict-mono-nonNeg : (p q : ℚ) (0≤p : 0ℚ ≤ p) (p<q : p < q)
                              → expq-total p <ℝ expq-total q
expq-total-strict-mono-nonNeg p q 0≤p p<q =
  let
    0≤q : 0ℚ ≤ q
    0≤q = ≤-trans 0≤p (<⇒≤ p<q)

    step : expq p 0≤p <ℝ expq q 0≤q
    step = expq-strict-mono p q 0≤p p<q
  in
    ≈-<-respʳ
      (≈ℝ-sym (expq-total-nonNeg q 0≤q))
      (≈-<-resp (≈ℝ-sym (expq-total-nonNeg p 0≤p)) step)

-- Both ends below zero: the reciprocal reverses the comparison of the
-- two positive exponentials, strictly.
--
-- 两端都在零点以下：倒数严格地反转两个正指数的比较。
expq-total-strict-mono-nonPos : (p q : ℚ) (p<0 : p < 0ℚ) (q<0 : q < 0ℚ)
                                (p<q : p < q)
                              → expq-total p <ℝ expq-total q
expq-total-strict-mono-nonPos p q p<0 q<0 p<q =
  let
    Pp : 0ℚ ≤ - p
    Pp = neg-of-nonpos {x = p} (<⇒≤ p<0)

    Qq : 0ℚ ≤ - q
    Qq = neg-of-nonpos {x = q} (<⇒≤ q<0)

    0<eP : 0ℝ <ℝ expq (- p) Pp
    0<eP = expq-pos (- p) Pp

    0<eQ : 0ℝ <ℝ expq (- q) Qq
    0<eQ = expq-pos (- q) Qq

    negq<negp : - q < - p
    negq<negp = neg-antimono-< {x = p} {y = q} p<q

    bndp : 0ℚ ≤ - p
    bndp = ≤-trans Qq (<⇒≤ negq<negp)

    eQ<eP : expq (- q) Qq <ℝ expq (- p) Pp
    eQ<eP = ≈-<-respʳ (expq-irr (- p) bndp Pp)
              (expq-strict-mono (- q) (- p) Qq negq<negp)

    step : recipℝ (expq (- p) Pp) 0<eP <ℝ recipℝ (expq (- q) Qq) 0<eQ
    step = recipℝ-strict-antitone-of (expq (- q) Qq) (expq (- p) Pp) 0<eQ 0<eP eQ<eP
  in
    ≈-<-respʳ
      (≈ℝ-sym (expq-total-as-inv q q<0))
      (≈-<-resp (≈ℝ-sym (expq-total-as-inv p p<0)) step)

-- Crossing zero: the left end is below one, the right end above it.
--
-- 跨越零点：左端小于一，右端大于一。
expq-total-strict-mono-cross : (p q : ℚ) (p<0 : p < 0ℚ) (0<q : 0ℚ < q)
                              → expq-total p <ℝ expq-total q
expq-total-strict-mono-cross p q p<0 0<q =
  <-trans (expq-total-lt-one p p<0) (expq-total-gt-one q 0<q)

-- Dispatch on the sign of the left end, then on the sign of the right.
--
-- 先按左端符号分派，再按右端符号分派。
expq-total-strict-mono-neg-branch : (p q : ℚ) (p<0 : p < 0ℚ)
    (t : Tri (0ℚ < q) (0ℚ ≡ q) (q < 0ℚ))
  → p < q → expq-total p <ℝ expq-total q
expq-total-strict-mono-neg-branch p q p<0 (tri< 0<q _ _) p<q =
  expq-total-strict-mono-cross p q p<0 0<q
expq-total-strict-mono-neg-branch p q p<0 (tri≈ _ eq _) p<q =
  ≈-<-respʳ
    (≈ℝ-trans (≈ℝ-sym expq-total-zero)
      (subst (λ z → expq-total 0ℚ ≈ℝ expq-total z) eq
        (≈ℝ-refl {expq-total 0ℚ})))
    (expq-total-lt-one p p<0)
expq-total-strict-mono-neg-branch p q p<0 (tri> _ _ q<0) p<q =
  expq-total-strict-mono-nonPos p q p<0 q<0 p<q

expq-total-strict-mono-branch : (p q : ℚ)
    (t : Tri (0ℚ < p) (0ℚ ≡ p) (p < 0ℚ))
  → p < q → expq-total p <ℝ expq-total q
expq-total-strict-mono-branch p q (tri< 0<p _ _) p<q =
  expq-total-strict-mono-nonNeg p q (<⇒≤ 0<p) p<q
expq-total-strict-mono-branch p q (tri≈ _ eq _) p<q =
  expq-total-strict-mono-nonNeg p q (≤-reflexive eq) p<q
expq-total-strict-mono-branch p q (tri> _ _ p<0) p<q =
  expq-total-strict-mono-neg-branch p q p<0 (<-cmp 0ℚ q) p<q

expq-total-strict-mono : (p q : ℚ) → p < q → expq-total p <ℝ expq-total q
expq-total-strict-mono p q p<q =
  expq-total-strict-mono-branch p q (<-cmp 0ℚ p) p<q
