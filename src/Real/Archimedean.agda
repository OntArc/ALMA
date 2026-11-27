------------------------------------------------------------------------
-- Archimedean precision selection for rational tolerances
--
-- 有理容差的阿基米德精度选择
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Archimedean where

open import Data.Empty using (⊥-elim)
open import Data.Integer using (+_; -[1+_]) renaming (+<+ to ℤ+<+)
open import Data.Integer.Properties using (<-irrefl) renaming (*-identityˡ to ℤ*-identityˡ)
open import Data.Nat using (ℕ; suc; _+_; s≤s; z≤n) renaming (_*_ to _ℕ*_)
open import Data.Nat.Properties as Nat using (≤-refl; m≤m+n)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _<_; _≤_; _*_; NonZero; *<*) renaming (_+_ to _+ℚ_)
open import Data.Rational.Base using (↥_; ↧_; ↧ₙ_; NonZero; Positive; positive; 1/_)
open import Data.Rational.Properties using
  (positive⁻¹; *-inverseˡ; *-inverseʳ; *-assoc; *-comm; *-identityˡ; *-identityʳ
  ; +-comm; +-identityˡ; +-identityʳ; +-monoˡ-<; +-mono-≤
  ; *-monoˡ-<-pos; pos*pos⇒pos; pos⇒nonZero; ≤-reflexive; ≤-trans; <-≤-trans; <-trans
  ; <⇒≤; ≤-<-trans; 1/pos⇒pos; *-monoˡ-≤-nonNeg; pos⇒nonNeg)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; cong; trans; refl; subst; subst₂; inspect; [_])
open import Relation.Nullary.Negation using (¬_)

open import Base.RationalRing using (swap-mid; 0≤1; 0<1)
open import Real using (ε; embed; 0<ε; 0<embed; embed-*; embed-mono-<; embed-mono-≤)

-- The denominator of the k-th precision is suc k.
--
-- 第 k 层精度的分母为 suc k。
den-eq : ∀ k → ↧ (ε k) ≡ + (suc k)
den-eq k = refl

-- Natural-number cross inequality.
--
-- 自然数交叉不等式：d 严格小于 (suc n) 与 (suc d) 的乘积。
cross : ∀ d n → d Data.Nat.< (suc n) ℕ* (suc d)
cross d n =
  let base : d Data.Nat.< suc d
      base = s≤s ≤-refl
      mult : suc d Data.Nat.≤ (suc n) ℕ* (suc d)
      mult = m≤m+n (suc d) (n ℕ* suc d)
  in Nat.<-≤-trans base mult

-- Numerator of a rational.
--
-- 有理数的分子。
num-of : ℚ → Data.Integer.ℤ
num-of x = ↥ x

-- Zero cannot satisfy the positive condition.
--
-- 零不满足此正性条件。
no-zero : ¬_ (+ 0 Data.Integer.< + 0 Data.Integer.* + 1)
no-zero = <-irrefl refl

-- Negative integers cannot satisfy the positive condition.
--
-- 负整数不满足该正性条件。
no-neg : ∀ n → ¬_ (+ 0 Data.Integer.< (-[1+ n ]) Data.Integer.* + 1)
no-neg n ()

-- For positive e, the precision at index ↧ₙ e has width strictly
-- below e.
--
-- 对正 e，精度索引 ↧ₙ e 处的层宽严格小于 e。
build : (e : ℚ) → 0ℚ < e → ε (↧ₙ e) < e
build e (*<* w) with num-of e | inspect num-of e
build e (*<* w) | + (suc n) | [ num-eq ] =
  let num = num-of e
      den = ↧ₙ e
      sd = + (suc den)
      all< = ℤ+<+ (cross den n)
      all<′ = subst (λ x → + den Data.Integer.< x Data.Integer.* sd)
                    (sym num-eq) all<
      lhs-eq = sym (ℤ*-identityˡ (↧ e))
      rhs-eq = cong (num Data.Integer.*_) (sym (den-eq den))
      aligned = subst₂ (λ a b → a Data.Integer.< b)
                      lhs-eq rhs-eq all<′
  in *<* aligned
build e (*<* w) | + 0 | _ = ⊥-elim (no-zero w)
build e (*<* w) | -[1+ n ] | _ = ⊥-elim (no-neg n w)

-- For every positive rational tolerance e there is a precision k whose
-- layer width ε k is strictly below e.
--
-- 对每个正有理容差 e，存在精度 k，使该层宽度 ε k 严格小于 e。
ε-archimedean : (e : ℚ) → 0ℚ < e → Σ ℕ (λ k → ε k < e)
ε-archimedean e pos = ↧ₙ e , build e pos

------------------------------------------------------------------------
-- The precision against its own denominator
--
-- 精度与其自身分母之积

-- ε j = 1/(j+1), so multiplying by the embedded successor recovers one.
--
-- ε j = 1/(j+1)，故乘以嵌入的后继得到一。
ε-den : (j : ℕ) → ε j * embed (suc j) ≡ 1ℚ
ε-den j = *-inverseˡ (embed (suc j))

------------------------------------------------------------------------
-- The precision bounded by one
--
-- 精度以一为界

-- The successor denominator is at least one, so the identity with the
-- embedded successor bounds every precision by one.
--
-- 后继分母不小于一，故与嵌入后继的恒等式把每一层精度限制在一以内。
ε-≤-1 : (j : ℕ) → ε j ≤ 1ℚ
ε-≤-1 j =
  let
    es : 1ℚ ≤ embed (suc j)
    es = embed-mono-≤ {m = 1} {n = suc j} (s≤s z≤n)

    e1 : ε j * 1ℚ ≡ ε j
    e1 = *-identityʳ (ε j)

    mono : ε j * 1ℚ ≤ ε j * embed (suc j)
    mono = *-monoˡ-≤-nonNeg (ε j) {{pos⇒nonNeg (ε j) {{positive (0<ε j)}}}} es

    step : ε j ≤ ε j * embed (suc j)
    step = subst (λ z → z ≤ ε j * embed (suc j)) e1 mono
  in
    subst (λ z → ε j ≤ z) (ε-den j) step

------------------------------------------------------------------------
-- A natural factor is absorbed by a deeper precision
--
-- 自然因子被更深的精度吸收

-- Multiply the strict comparison (N+1)(k+1) < j+1 by the positive pair
-- ε j, ε k. The two denominators cancel against their own precisions, so
-- the product comparison is exactly `embed (N+1) * ε j < ε k`.
--
-- 把严格比较 (N+1)(k+1) < j+1 乘以正的一对 ε j、ε k。两个分母各自与自身
-- 精度相消，故乘积比较恰为 `embed (N+1) * ε j < ε k`。
ε-scale : (N k : ℕ) → Σ ℕ (λ j → embed (suc N) * ε j < ε k)
ε-scale N k =
  let
    j : ℕ
    j = suc N ℕ* suc k

    A : ℚ
    A = embed (suc N)

    P : ℚ
    P = embed (suc k)

    Q : ℚ
    Q = ε j

    R : ℚ
    R = ε k

    J : ℚ
    J = embed (suc j)

    key : A * P < J
    key = subst (λ z → z < J) (sym (embed-* (suc N) (suc k)))
            (embed-mono-< {m = suc N ℕ* suc k} {n = suc j} ≤-refl)

    C : ℚ
    C = Q * R

    0<C : 0ℚ < C
    0<C = positive⁻¹ C {{pos*pos⇒pos Q {{positive (0<ε j)}} R {{positive (0<ε k)}}}}

    mult : (A * P) * C < J * C
    mult = *-monoˡ-<-pos C {{positive 0<C}} key

    PQ : P * R ≡ 1ℚ
    PQ = *-inverseʳ P

    JQ : J * Q ≡ 1ℚ
    JQ = *-inverseʳ J

    lhsEq : (A * P) * (Q * R) ≡ A * Q
    lhsEq = trans (swap-mid A P Q R)
              (trans (cong (λ z → (A * Q) * z) PQ) (*-identityʳ (A * Q)))

    rhsEq : J * (Q * R) ≡ R
    rhsEq = trans (sym (*-assoc J Q R))
              (trans (cong (λ z → z * R) JQ) (*-identityˡ R))

    goal : A * Q < R
    goal = subst₂ _<_ lhsEq rhsEq mult
  in
    j , goal

------------------------------------------------------------------------
-- Strict comparison against a shifted right endpoint
--
-- 与右移端点的严格比较

-- A local copy of the standard "x < x + y" fact for positive y, kept
-- here because the interval layer sits above this module.
--
-- 标准事实「x < x + y」（y 为正）的本地副本，留在本模块，因为区间层位于本模块之上。
le-add-right : (x y : ℚ) → 0ℚ ≤ y → x ≤ x +ℚ y
le-add-right x y 0≤y =
  ≤-trans (≤-reflexive (sym (+-identityʳ x))) (+-mono-≤ {x} {x} {0ℚ} {y} (≤-reflexive refl) 0≤y)

lt-add-right : (x : ℚ) {y : ℚ} → 0ℚ < y → x < x +ℚ y
lt-add-right x {y} 0<y =
  subst₂ _<_ (+-identityˡ x) (+-comm y x) (+-monoˡ-< x 0<y)

------------------------------------------------------------------------
-- Every nonnegative rational sits below a natural
--
-- 每个非负有理数都在某个自然数之下

-- Apply `ε-archimedean` to the reciprocal 1/(1+B). Multiplying the
-- resulting ε comparison by the positive product (1+j)(1+B) cancels
-- both denominators against their own precisions, as in `ε-scale`,
-- leaving 1+B < j+1, hence B below the natural successor.
--
-- 把 `ε-archimedean` 用在倒数 1/(1+B)。把所得的 ε 比较乘以正积 (1+j)(1+B)，
-- 两个分母各自与自身精度相消，如 `ε-scale`，剩下 1+B < j+1，故 B 低于该自然后继。
recipℚ : (q : ℚ) ⦃ nz : NonZero q ⦄ → ℚ
recipℚ q ⦃ nz ⦄ = 1/ q

rat-under-nat : (B : ℚ) → 0ℚ ≤ B → Σ ℕ (λ N → B ≤ embed (suc N))
rat-under-nat B 0≤B =
  let
    q : ℚ
    q = 1ℚ +ℚ B

    1≤q : 1ℚ ≤ q
    1≤q = le-add-right 1ℚ B 0≤B

    0<q : 0ℚ < q
    0<q = <-≤-trans 0<1 1≤q

    pq : Positive q
    pq = positive 0<q

    qnz : NonZero q
    qnz = pos⇒nonZero q {{pq}}

    e : ℚ
    e = recipℚ q ⦃ qnz ⦄

    pe : Positive e
    pe = 1/pos⇒pos q {{pq}}

    0<e : 0ℚ < e
    0<e = positive⁻¹ e {{pe}}

    w : Σ ℕ (λ j → ε j < e)
    w = ε-archimedean e 0<e

    j : ℕ
    j = proj₁ w

    h : ε j < e
    h = proj₂ w

    X : ℚ
    X = embed (suc j)

    C : ℚ
    C = X * q

    0<X : 0ℚ < X
    0<X = 0<embed j

    pC : Positive C
    pC = pos*pos⇒pos X {{positive 0<X}} q {{pq}}

    0<C : 0ℚ < C
    0<C = positive⁻¹ C {{pC}}

    mult : ε j * C < e * C
    mult = *-monoˡ-<-pos C {{positive 0<C}} h

    lhs : ε j * C ≡ q
    lhs = trans (trans (sym (*-assoc (ε j) X q))
                  (cong (λ z → z * q) (ε-den j))) (*-identityˡ q)

    rhs : e * C ≡ X
    rhs = trans (sym (*-assoc e X q))
            (trans (cong (λ z → z * q) (*-comm e X))
              (trans (*-assoc X e q)
                (trans (cong (λ z → X * z) (*-inverseˡ q ⦃ qnz ⦄)) (*-identityʳ X))))

    key : q < X
    key = subst₂ _<_ lhs rhs mult

    small : B < X
    small = <-trans
              (subst (λ z → B < z) (+-comm B 1ℚ) (lt-add-right B {1ℚ} 0<1))
              key

    out : B ≤ embed (suc j)
    out = <⇒≤ small
  in
    j , out

------------------------------------------------------------------------
-- A precision whose product with a rational factor stays below a target
--
-- 与有理因子之积仍低于目标的精度

-- Given a nonnegative factor c and a positive rational target t, bound
-- c by a natural successor N+1 and pass to the strictly larger N+2. A
-- deeper precision then absorbs N+2 into ε k, with ε k itself below t,
-- and commutativity of the rational product carries the comparison over
-- to ε j * c.
--
-- 给定非负因子 c 与正有理目标 t，先把 c 压到某个自然后继 N+1 之下，
-- 再上移到严格更大的 N+2；随后用更深的精度把 N+2 吸收到 ε k 之下，
-- 而 ε k 本身又低于 t。有理乘法的交换律再把比较搬到 ε j * c 上。
rat-shrink : (c : ℚ) (0≤c : 0ℚ ≤ c) (t : ℚ) (0<t : 0ℚ < t)
           → Σ ℕ (λ j → ε j * c < t)
rat-shrink c 0≤c t 0<t =
  let
    n : Σ ℕ (λ N → c ≤ embed (suc N))
    n = rat-under-nat c 0≤c

    N : ℕ
    N = proj₁ n

    c≤A₁ : c ≤ embed (suc N)
    c≤A₁ = proj₂ n

    A₁ : ℚ
    A₁ = embed (suc N)

    A₂ : ℚ
    A₂ = embed (suc (suc N))

    A₁<A₂ : A₁ < A₂
    A₁<A₂ = embed-mono-< {m = suc N} {n = suc (suc N)} (s≤s ≤-refl)

    c<A₂ : c < A₂
    c<A₂ = ≤-<-trans c≤A₁ A₁<A₂

    w : Σ ℕ (λ k → ε k < t)
    w = ε-archimedean t 0<t

    k : ℕ
    k = proj₁ w

    εk<t : ε k < t
    εk<t = proj₂ w

    s : Σ ℕ (λ j → embed (suc (suc N)) * ε j < ε k)
    s = ε-scale (suc N) k

    j : ℕ
    j = proj₁ s

    A₂εj<εk : A₂ * ε j < ε k
    A₂εj<εk = proj₂ s

    0<εj : 0ℚ < ε j
    0<εj = 0<ε j

    pej : Positive (ε j)
    pej = positive 0<εj

    cεj<A₂εj : c * ε j < A₂ * ε j
    cεj<A₂εj = *-monoˡ-<-pos (ε j) {{pej}} c<A₂

    cεj<εk : c * ε j < ε k
    cεj<εk = <-trans cεj<A₂εj A₂εj<εk

    εjc<εk : ε j * c < ε k
    εjc<εk = subst (λ z → z < ε k) (sym (*-comm (ε j) c)) cεj<εk
  in
    j , <-trans εjc<εk εk<t
