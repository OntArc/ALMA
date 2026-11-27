------------------------------------------------------------------------
-- Laws of the real exponential
--
-- 实指数的定律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Elementary.ExpLaws where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_; _*_)
open import Data.Rational.Properties using (≤-refl; ≤-trans; ≤-reflexive; <⇒≤)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Base.RationalRing using (0<1)
open import Real using (embed; 0<embed)
open import Real.Archimedean using (rat-under-nat; le-add-right)
open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ; 1ℝ; _+ℝ_; _-ℝ_)
open import Real.Interval.ArithLaws using
  (+ℝ-identityˡ; +ℝ-identityʳ; sub-add-cancelℝ)
open import Real.Interval.Continuity using (0<embedℚ; Close)
open import Real.Interval.DensityArch using (dense)
open import Real.Interval.Embed using (0ℝ<ℝ1ℝ)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Elementary.Exp using
  (Pℝ; Pℝ-member; Pℝ-zero; Pℝ-isUpper; located; expℝ; expℝ-upper; expℝ-least
  ; expℝ-le-of-partials)
open import Real.Interval.Elementary.ExpRat using
  (expℝ-at-rat; embed-nonNeg; expPartialℝ-at-rat)
open import Real.Interval.Exp.Series using
  (termℝ; expPartialℝ; expPartialℝ-mono)
open import Real.Interval.Exp.Lipschitz using (expPartial-bound; expq-close)
open import Real.Interval.Exp.Core using (expPartial; expq; expPartial-zero)
open import Real.Interval.Exp.Order using (expPartial-one; expq-strict-mono)
open import Real.Interval.Mul.Cong using (*ℝ-cong)
open import Real.Interval.Mul.Laws using (*ℝ-zeroˡ; *ℝ-zeroʳ)
open import Real.Interval.Mul.Order using (+ℝ-cong; ≈-<-respʳ)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderLaws using (<-+mono; ≈-<-resp)
open import Real.Interval.OrderComplete using (sup-member-of-lt)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.OrderLe using
  (≤ℝ-refl; <⇒≤ℝ; ≈⇒≤ℝ; ≤ℝ-antisym; ≤ℝ-<trans; <-≤ℝ-trans; sub-pos-lt
  ; <-+mono-reflect; ≤ℝ-+-mono)
open import Real.Interval.Recip using (recipℝ)
open import Real.Interval.Series.Alternating using (sum-mono)
open import Real.Interval.Sqrt.Bounds using (embedℚ-reflect; embedℚ-≤)

------------------------------------------------------------------------
-- Congruence of the real series in the argument
--
-- 实数级数在自变量上的同余

-- Each step multiplies by x and by a fixed positive reciprocal of the
-- increment, so congruence only needs congruence of multiplication.
--
-- 每一步乘 x 与固定增量的正倒数，故同余只需要乘法的同余。
termℝ-cong : (x x' : RealI) → x ≈ℝ x' → (k : ℕ)
           → termℝ x k ≈ℝ termℝ x' k
termℝ-cong x x' x≈ zero = ≈ℝ-refl
termℝ-cong x x' x≈ (suc k) =
  *ℝ-cong (*ℝ-cong (termℝ-cong x x' x≈ k) x≈) ≈ℝ-refl

expPartialℝ-cong : (x x' : RealI) → x ≈ℝ x'
                 → (n : ℕ) → expPartialℝ x n ≈ℝ expPartialℝ x' n
expPartialℝ-cong x x' x≈ n =
  ≤ℝ-antisym
    (sum-mono (termℝ x) (termℝ x')
      (λ k → ≈⇒≤ℝ (termℝ-cong x x' x≈ k)) n)
    (sum-mono (termℝ x') (termℝ x)
      (λ k → ≈⇒≤ℝ (≈ℝ-sym (termℝ-cong x x' x≈ k))) n)

------------------------------------------------------------------------
-- The cut is congruent in the argument
--
-- 割在自变量上同余

Pℝ-cong : (x x' : RealI) (0≤x : 0ℝ ≤ℝ x) (0≤x' : 0ℝ ≤ℝ x')
        → x ≈ℝ x' → (r : RealI)
        → Pℝ x 0≤x r → Pℝ x' 0≤x' r
Pℝ-cong x x' 0≤x 0≤x' x≈ r (q , (r≈ , n , q≤n)) =
  q , ( r≈
      , n
      , ≤ℝ-trans q≤n (≈⇒≤ℝ (expPartialℝ-cong x x' x≈ n)) )

expℝ-cong : (x x' : RealI) (0≤x : 0ℝ ≤ℝ x) (0≤x' : 0ℝ ≤ℝ x')
          → x ≈ℝ x'
          → expℝ x 0≤x ≈ℝ expℝ x' 0≤x'
expℝ-cong x x' 0≤x 0≤x' x≈ =
  ≤ℝ-antisym
    (expℝ-least x 0≤x (expℝ x' 0≤x')
      (λ r pr → expℝ-upper x' 0≤x' r (Pℝ-cong x x' 0≤x 0≤x' x≈ r pr)))
    (expℝ-least x' 0≤x' (expℝ x 0≤x)
      (λ r pr → expℝ-upper x 0≤x r (Pℝ-cong x' x 0≤x' 0≤x (≈ℝ-sym x≈) r pr)))

------------------------------------------------------------------------
-- The series at zero
--
-- 零处的级数

-- Every term from index one on vanishes, so the partial sums from
-- index one on are all one, and the rational partial sums stay at most
-- one.
--
-- 从下标一起每一项都消失，故从下标一起的部分和全是一，有理部分和
-- 始终不超过一。
termℝ-zero : (k : ℕ) → termℝ 0ℝ (suc k) ≈ℝ 0ℝ
termℝ-zero k =
  ≈ℝ-trans (*ℝ-cong (*ℝ-zeroʳ (termℝ 0ℝ k)) ≈ℝ-refl)
    (*ℝ-zeroˡ (recipℝ (embedℚ (embed (suc k)))
      (0<embedℚ (embed (suc k)) (0<embed k))))

expPartialℝ-zero-suc : (m : ℕ) → expPartialℝ 0ℝ (suc m) ≈ℝ 1ℝ
expPartialℝ-zero-suc zero = +ℝ-identityˡ 1ℝ
expPartialℝ-zero-suc (suc m) =
  ≈ℝ-trans
    (+ℝ-cong (expPartialℝ-zero-suc m) (termℝ-zero m))
    (+ℝ-identityʳ 1ℝ)

expPartialℝ-zero-le : (n : ℕ) → expPartialℝ 0ℝ n ≤ℝ 1ℝ
expPartialℝ-zero-le zero = <⇒≤ℝ 0ℝ<ℝ1ℝ
expPartialℝ-zero-le (suc m) = ≈⇒≤ℝ (expPartialℝ-zero-suc m)

expPartial-zero-le-one : (n : ℕ) → expPartial 0ℚ n ≤ 1ℚ
expPartial-zero-le-one zero = ≤-trans (≤-refl {0ℚ}) (<⇒≤ 0<1)
expPartial-zero-le-one (suc m) = ≤-reflexive (expPartial-one m)

------------------------------------------------------------------------
-- exp at zero is one
--
-- 零处的 exp 为一

-- The embedded one is a member at index one, which gives the lower
-- bound; the upper bound comes from expPartialℝ-zero-le at every index.
--
-- 嵌入的一在下标一处是成员，给出下界；上界由每个下标上的
-- expPartialℝ-zero-le 给出。
expℝ-zero : expℝ 0ℝ (≤ℝ-refl {0ℝ}) ≈ℝ 1ℝ
expℝ-zero =
  let
    z≤ : 0ℝ ≤ℝ 0ℝ
    z≤ = ≤ℝ-refl {0ℝ}

    member : Pℝ 0ℝ z≤ (embedℚ 1ℚ)
    member = Pℝ-member 0ℝ z≤ 1ℚ
      (suc zero , ≤ℝ-trans (≤ℝ-refl {1ℝ})
        (≈⇒≤ℝ (≈ℝ-sym (expPartialℝ-zero-suc zero))))

    lower : 1ℝ ≤ℝ expℝ 0ℝ z≤
    lower = expℝ-upper 0ℝ z≤ (embedℚ 1ℚ) member

    upper : expℝ 0ℝ z≤ ≤ℝ 1ℝ
    upper = expℝ-least 0ℝ z≤ 1ℝ
      (λ r (q , (r≈ , n , q≤n)) →
        ≤ℝ-trans (≈⇒≤ℝ r≈)
          (≤ℝ-trans q≤n (expPartialℝ-zero-le n)))
  in
    ≈ℝ-sym (≤ℝ-antisym lower upper)

------------------------------------------------------------------------
-- The partial sums lie below the cut
--
-- 部分和落在割之下

-- If the cut were below some partial sum, density would give a rational
-- strictly between them; that rational is a member of the cut at the
-- same index, hence lies below the cut, a contradiction.
--
-- 若割低于某个部分和，稠密性给出严格居中的有理点；该有理点在同一个
-- 下标上是割的成员，故在割之下，矛盾。
expPartialℝ-le-expℝ : (x : RealI) (0≤x : 0ℝ ≤ℝ x) (n : ℕ)
                    → expPartialℝ x n ≤ℝ expℝ x 0≤x
expPartialℝ-le-expℝ x 0≤x n exp<pn =
  let
    d : Σ ℚ (λ q → (expℝ x 0≤x <ℝ embedℚ q)
             × (embedℚ q <ℝ expPartialℝ x n))
    d = dense exp<pn

    q : ℚ
    q = proj₁ d

    sup<q : expℝ x 0≤x <ℝ embedℚ q
    sup<q = proj₁ (proj₂ d)

    q<pn : embedℚ q <ℝ expPartialℝ x n
    q<pn = proj₂ (proj₂ d)

    member : Pℝ x 0≤x (embedℚ q)
    member = Pℝ-member x 0≤x q (n , <⇒≤ℝ q<pn)

    q≤sup : embedℚ q ≤ℝ expℝ x 0≤x
    q≤sup = expℝ-upper x 0≤x (embedℚ q) member
  in
    q≤sup sup<q

------------------------------------------------------------------------
-- Monotonicity of the cut
--
-- 割的单调性

-- A member of the cut at x is a rational below a partial sum at x;
-- that partial sum is below the corresponding one at x', which lies
-- below the cut at x'.
--
-- x 处割的成员是某个有理点，它不超过 x 处的部分和；该部分和不超过
-- x' 处对应的部分和，后者在 x' 的割之下。
expℝ-mono : (x x' : RealI) (0≤x : 0ℝ ≤ℝ x) (0≤x' : 0ℝ ≤ℝ x')
          → x ≤ℝ x' → expℝ x 0≤x ≤ℝ expℝ x' 0≤x'
expℝ-mono x x' 0≤x 0≤x' x≤x' =
  expℝ-least x 0≤x (expℝ x' 0≤x')
    (λ r (q , (r≈ , n , q≤n)) →
      ≤ℝ-trans (≈⇒≤ℝ r≈)
        (≤ℝ-trans q≤n
          (≤ℝ-trans (expPartialℝ-mono x x' 0≤x x≤x' n)
            (expPartialℝ-le-expℝ x' 0≤x' n))))

------------------------------------------------------------------------
-- Lower bounds of the cut
--
-- 割的下界

-- Index zero contributes nothing, so the cut is above zero; index one
-- contributes exactly one, so the cut is above one.
--
-- 下标零无贡献，故割在零之上；下标一恰好贡献一，故割在一之上。
expℝ-nonNeg : (x : RealI) (0≤x : 0ℝ ≤ℝ x) → 0ℝ ≤ℝ expℝ x 0≤x
expℝ-nonNeg x 0≤x = expPartialℝ-le-expℝ x 0≤x zero

expℝ-ge-one : (x : RealI) (0≤x : 0ℝ ≤ℝ x) → 1ℝ ≤ℝ expℝ x 0≤x
expℝ-ge-one x 0≤x =
  expℝ-upper x 0≤x (embedℚ 1ℚ)
    (Pℝ-member x 0≤x 1ℚ
      (suc zero , ≤ℝ-trans (≤ℝ-refl {1ℝ})
        (≈⇒≤ℝ (≈ℝ-sym (+ℝ-identityˡ 1ℝ)))))

------------------------------------------------------------------------
-- Strict monotonicity
--
-- 严格单调

-- Sandwiched between x and y are two rational points r < p, so that
-- x < embed r < embed p < y. Monotonicity of the cut gives the outer
-- two steps, the identity at rational points turns the middle into the
-- strict monotonicity of `expq`, and the strictness is carried out by
-- the mixed transitivity lemmas.
--
-- 在 x 与 y 之间夹两个有理点 r < p，使 x < embed r < embed p < y。割的
-- 单调性给出外侧两步，有理点处的同一性把中间化成 expq 的严格单调性，
-- 严格性由混合传递引理逐段带出。
expℝ-strict-mono : (x y : RealI) (0≤x : 0ℝ ≤ℝ x) (0≤y : 0ℝ ≤ℝ y)
                 → x <ℝ y → expℝ x 0≤x <ℝ expℝ y 0≤y
expℝ-strict-mono x y 0≤x 0≤y x<y =
  let
    p , (x<p , p<y) = dense {x = x} {y = y} x<y

    r , (x<r , r<pEmb) = dense {x = x} {y = embedℚ p} x<p

    r<p : r < p
    r<p = embedℚ-reflect r p r<pEmb

    0<r : 0ℚ < r
    0<r = embedℚ-reflect 0ℚ r (≤ℝ-<trans {x = 0ℝ} {y = x} {z = embedℚ r} 0≤x x<r)

    0≤r : 0ℚ ≤ r
    0≤r = <⇒≤ 0<r

    0≤p : 0ℚ ≤ p
    0≤p = ≤-trans 0≤r (<⇒≤ r<p)

    0≤er : 0ℝ ≤ℝ embedℚ r
    0≤er = embed-nonNeg r 0≤r

    0≤ep : 0ℝ ≤ℝ embedℚ p
    0≤ep = embed-nonNeg p 0≤p

    a : expℝ x 0≤x ≤ℝ expℝ (embedℚ r) 0≤er
    a = expℝ-mono x (embedℚ r) 0≤x 0≤er (<⇒≤ℝ x<r)

    b : expℝ (embedℚ r) 0≤er ≤ℝ expq r 0≤r
    b = ≈⇒≤ℝ (expℝ-at-rat r 0≤r)

    c : expq r 0≤r <ℝ expq p 0≤p
    c = expq-strict-mono r p 0≤r r<p

    d : expq p 0≤p ≤ℝ expℝ (embedℚ p) 0≤ep
    d = ≈⇒≤ℝ (≈ℝ-sym (expℝ-at-rat p 0≤p))

    e : expℝ (embedℚ p) 0≤ep ≤ℝ expℝ y 0≤y
    e = expℝ-mono (embedℚ p) y 0≤ep 0≤y (<⇒≤ℝ p<y)

    ab : expℝ x 0≤x ≤ℝ expq r 0≤r
    ab = ≤ℝ-trans {x = expℝ x 0≤x} {y = expℝ (embedℚ r) 0≤er}
           {z = expq r 0≤r} a b

    abc : expℝ x 0≤x <ℝ expq p 0≤p
    abc = ≤ℝ-<trans ab c

    abcd : expℝ x 0≤x <ℝ expℝ (embedℚ p) 0≤ep
    abcd = <-≤ℝ-trans abc d
  in
    <-≤ℝ-trans abcd e

------------------------------------------------------------------------
-- The cut is approached by its partial sums
--
-- 割由部分和逼近

-- `expℝ` is the least upper bound of the partial sums. A point strictly
-- below the cut therefore has a member above it, and every member is an
-- embedded rational dominated by some partial sum. Subtracting a rational
-- budget `d` keeps the point strictly below the cut, so the member found
-- there pushes the cut strictly below `partial + d`. This is the half of
-- the sandwich that `expPartialℝ-le-expℝ` does not give, and it is what
-- turns worst-case estimates at the cut into estimates at the partial
-- sums.
--
-- `expℝ` 是部分和的最小上界。故严格在割之下的点必有成员压在其上，而每个成员
-- 都是被某个部分和支配的嵌入有理数。减去有理预算 `d` 仍使该点在割之下，于是
-- 在那里找到的成员把割推到 `部分和 + d` 之下。这正是不由
-- `expPartialℝ-le-expℝ` 给出的那一半夹逼，也是把割处的最坏情形估计转成部分和
-- 处估计的依据。
expPartialℝ-approx : (x : RealI) (0≤x : 0ℝ ≤ℝ x) (d : ℚ) (0<d : 0ℚ < d)
                   → Σ ℕ (λ n → expℝ x 0≤x ≤ℝ expPartialℝ x n +ℝ embedℚ d)
expPartialℝ-approx x 0≤x d 0<d =
  let
    E : RealI
    E = embedℚ d

    0<E : 0ℝ <ℝ E
    0<E = 0<embedℚ d 0<d

    y : RealI
    y = expℝ x 0≤x -ℝ E

    y<S : y <ℝ expℝ x 0≤x
    y<S = sub-pos-lt (expℝ x 0≤x) E 0<E

    wk : Σ RealI (λ z → Pℝ x 0≤x z × (y <ℝ z))
    wk = sup-member-of-lt {P = Pℝ x 0≤x} (located x 0≤x) (Pℝ-zero x 0≤x)
           (Pℝ-isUpper x 0≤x) y y<S

    z : RealI
    z = proj₁ wk

    pz : Pℝ x 0≤x z
    pz = proj₁ (proj₂ wk)

    y<z : y <ℝ z
    y<z = proj₂ (proj₂ wk)

    q : ℚ
    q = proj₁ pz

    z≈q : z ≈ℝ embedℚ q
    z≈q = proj₁ (proj₂ pz)

    nm : Σ ℕ (λ n → embedℚ q ≤ℝ expPartialℝ x n)
    nm = proj₂ (proj₂ pz)

    m : ℕ
    m = proj₁ nm

    q≤Pm : embedℚ q ≤ℝ expPartialℝ x m
    q≤Pm = proj₂ nm

    y<q : y <ℝ embedℚ q
    y<q = ≈-<-respʳ z≈q y<z

    y<Pm : y <ℝ expPartialℝ x m
    y<Pm = <-≤ℝ-trans y<q q≤Pm

    step : y +ℝ E <ℝ expPartialℝ x m +ℝ E
    step = <-+mono y (expPartialℝ x m) E y<Pm

    collapse : y +ℝ E ≈ℝ expℝ x 0≤x
    collapse = sub-add-cancelℝ (expℝ x 0≤x) E

    S<PmE : expℝ x 0≤x <ℝ expPartialℝ x m +ℝ E
    S<PmE = ≈-<-resp collapse step
  in
    m , <⇒≤ℝ S<PmE

------------------------------------------------------------------------
-- The exponential is positive
--
-- 指数为正

-- One is a member bound of the cut, so the cut itself stays above one.
--
-- 一是割的成员界，故割本身始终在一之上。
expℝ-pos : (x : RealI) (0≤x : 0ℝ ≤ℝ x) → 0ℝ <ℝ expℝ x 0≤x
expℝ-pos x 0≤x = <-≤ℝ-trans 0ℝ<ℝ1ℝ (expℝ-ge-one x 0≤x)

------------------------------------------------------------------------
-- Partial sums at an arbitrary point are uniformly bounded by a rational
--
-- 任意点处部分和被一个有理数一致界住

-- Move the point into a rational window from above: monotonicity of the
-- partial sums compares them with the values at the rational endpoint,
-- and the rational endpoint carries the bound `expPartial-bound`. The
-- bound therefore does not depend on `n`.
--
-- 把点移到上方的有理窗：部分和的单调性把它们与有理端点处的值比较，而有理
-- 端点带有界 `expPartial-bound`。该界因此不依赖于 `n`。
expPartialℝ-bound : (x : RealI) (0≤x : 0ℝ ≤ℝ x)
                    (p : ℚ) (0≤p : 0ℚ ≤ p) (x≤p : x ≤ℝ embedℚ p)
                    (d : ℚ) (0<d : 0ℚ < d)
                  → Σ ℚ (λ B → (n : ℕ) → expPartialℝ x n ≤ℝ embedℚ B)
expPartialℝ-bound x 0≤x p 0≤p x≤p d 0<d =
  let
    pb : Σ ℚ (λ B → (n : ℕ) → expPartial p n ≤ B)
    pb = expPartial-bound p 0≤p d 0<d

    B : ℚ
    B = proj₁ pb

    bnd : (n : ℕ) → expPartial p n ≤ B
    bnd = proj₂ pb
  in
    B , λ n →
      ≤ℝ-trans (expPartialℝ-mono x (embedℚ p) 0≤x x≤p n)
        (≤ℝ-trans (≈⇒≤ℝ (expPartialℝ-at-rat p 0≤p n))
          (embedℚ-≤ (expPartial p n) B (bnd n)))

------------------------------------------------------------------------
-- The cut itself is bounded by the same rational
--
-- 割本身被同一个有理数界住

expℝ-bound : (x : RealI) (0≤x : 0ℝ ≤ℝ x)
             (p : ℚ) (0≤p : 0ℚ ≤ p) (x≤p : x ≤ℝ embedℚ p)
             (d : ℚ) (0<d : 0ℚ < d)
           → Σ ℚ (λ B → expℝ x 0≤x ≤ℝ embedℚ B)
expℝ-bound x 0≤x p 0≤p x≤p d 0<d =
  let
    b : Σ ℚ (λ B → (n : ℕ) → expPartialℝ x n ≤ℝ embedℚ B)
    b = expPartialℝ-bound x 0≤x p 0≤p x≤p d 0<d
  in
    proj₁ b , expℝ-le-of-partials x 0≤x (embedℚ (proj₁ b)) (proj₂ b)


------------------------------------------------------------------------
-- Natural-form uniform bounds on a rational window
--
-- 有理窗上的自然数形式一致界

-- The rational bound of `expPartial-bound` / `expℝ-bound` is reshaped
-- into `embed (suc N)`, the form consumed by the ε-budget lemma
-- `ε-scale`. The bridge is `rat-under-nat`; its nonnegativity side
-- condition is read off `bnd zero` together with `expPartial-zero`, so
-- no order reflection through the embedding is needed here.
--
-- expPartial-bound / expℝ-bound 的有理界被改写成 `embed (suc N)`,
-- 即 ε 预算引理 `ε-scale` 所消费的形式。桥是 `rat-under-nat`；其非负
-- 前提由 `bnd zero` 与 `expPartial-zero` 读出，无需序在嵌入下的反射。
expPartialℝ-bound-nat : (x : RealI) (0≤x : 0ℝ ≤ℝ x)
                        (p : ℚ) (0≤p : 0ℚ ≤ p) (x≤p : x ≤ℝ embedℚ p)
                        (d : ℚ) (0<d : 0ℚ < d)
                      → Σ ℕ (λ N → (n : ℕ) → expPartialℝ x n ≤ℝ embedℚ (embed (suc N)))
expPartialℝ-bound-nat x 0≤x p 0≤p x≤p d 0<d =
  let
    pb : Σ ℚ (λ B → (n : ℕ) → expPartial p n ≤ B)
    pb = expPartial-bound p 0≤p d 0<d

    B : ℚ
    B = proj₁ pb

    bnd : (n : ℕ) → expPartial p n ≤ B
    bnd = proj₂ pb

    0≤B : 0ℚ ≤ B
    0≤B = subst (λ z → z ≤ B) (expPartial-zero p) (bnd zero)

    nb : Σ ℕ (λ N → B ≤ embed (suc N))
    nb = rat-under-nat B 0≤B

    N : ℕ
    N = proj₁ nb

    b≤ : B ≤ embed (suc N)
    b≤ = proj₂ nb
  in
    N , λ n →
      ≤ℝ-trans (expPartialℝ-mono x (embedℚ p) 0≤x x≤p n)
        (≤ℝ-trans (≈⇒≤ℝ (expPartialℝ-at-rat p 0≤p n))
          (embedℚ-≤ (expPartial p n) (embed (suc N))
            (≤-trans (bnd n) b≤)))

------------------------------------------------------------------------
-- The cut is bounded by the same natural
--
-- 割本身被同一个自然数界住

expℝ-bound-nat : (x : RealI) (0≤x : 0ℝ ≤ℝ x)
                 (p : ℚ) (0≤p : 0ℚ ≤ p) (x≤p : x ≤ℝ embedℚ p)
                 (d : ℚ) (0<d : 0ℚ < d)
               → Σ ℕ (λ N → expℝ x 0≤x ≤ℝ embedℚ (embed (suc N)))
expℝ-bound-nat x 0≤x p 0≤p x≤p d 0<d =
  let
    b : Σ ℕ (λ N → (n : ℕ) → expPartialℝ x n ≤ℝ embedℚ (embed (suc N)))
    b = expPartialℝ-bound-nat x 0≤x p 0≤p x≤p d 0<d

    N : ℕ
    N = proj₁ b

    bnd : (n : ℕ) → expPartialℝ x n ≤ℝ embedℚ (embed (suc N))
    bnd = proj₂ b
  in
    N , expℝ-le-of-partials x 0≤x (embedℚ (embed (suc N))) bnd

------------------------------------------------------------------------
-- Rational drift at real level
--
-- 实数层的有理漂移估计

-- `expq-close` lives at the cut level. This is its transfer to `expℝ`
-- at rational points, obtained by rewriting both endpoints through
-- `expℝ-at-rat`. The subtraction congruence is not needed: the first
-- component is recovered from `x < y + d` via `sub-add-cancelℝ` and
-- `<-+mono-reflect`.
--
-- expq-close 工作在割层。这里把它搬到有理点处的 expℝ：两端各经
-- expℝ-at-rat 改写。不需要减法的同余：第一分量由 `x < y + d` 经
-- sub-add-cancelℝ 与 <-+mono-reflect 还原。
expℝ-close-rat : (p h : ℚ) (0≤p : 0ℚ ≤ p) (0≤h : 0ℚ ≤ h) (B : ℚ)
                 (bnd : (j : ℕ) → expPartial (p + h) j ≤ B)
                 (e : ℚ) (0<e : 0ℚ < e)
               → Close (h * (1ℚ + B) + e)
                       (expℝ (embedℚ p) (embed-nonNeg p 0≤p))
                       (expℝ (embedℚ (p + h)) (embed-nonNeg (p + h) (≤-trans 0≤p (le-add-right p h 0≤h))))
expℝ-close-rat p h 0≤p 0≤h B bnd e 0<e =
  let
    0≤ph : 0ℚ ≤ p + h
    0≤ph = ≤-trans 0≤p (le-add-right p h 0≤h)

    d : ℚ
    d = h * (1ℚ + B) + e

    X : RealI
    X = expq p 0≤p

    Y : RealI
    Y = expq (p + h) 0≤ph

    P : RealI
    P = expℝ (embedℚ p) (embed-nonNeg p 0≤p)

    Q : RealI
    Q = expℝ (embedℚ (p + h)) (embed-nonNeg (p + h) 0≤ph)

    X≈P : X ≈ℝ P
    X≈P = ≈ℝ-sym (expℝ-at-rat p 0≤p)

    Y≈Q : Y ≈ℝ Q
    Y≈Q = ≈ℝ-sym (expℝ-at-rat (p + h) 0≤ph)

    c : Close d X Y
    c = expq-close p h 0≤p 0≤h B bnd e 0<e

    c1 : X -ℝ embedℚ d <ℝ Y
    c1 = proj₁ c

    c2 : Y <ℝ X +ℝ embedℚ d
    c2 = proj₂ c

    step : (X -ℝ embedℚ d) +ℝ embedℚ d <ℝ Y +ℝ embedℚ d
    step = <-+mono (X -ℝ embedℚ d) Y (embedℚ d) c1

    X<Yd : X <ℝ Y +ℝ embedℚ d
    X<Yd = ≈-<-resp (sub-add-cancelℝ X (embedℚ d)) step

    P<Qd : P <ℝ Q +ℝ embedℚ d
    P<Qd = ≈-<-resp X≈P
             (≈-<-respʳ (+ℝ-cong Y≈Q (≈ℝ-refl {embedℚ d})) X<Yd)

    shifted : (P -ℝ embedℚ d) +ℝ embedℚ d <ℝ Q +ℝ embedℚ d
    shifted = ≈-<-resp (≈ℝ-sym (sub-add-cancelℝ P (embedℚ d))) P<Qd

    PdQ : P -ℝ embedℚ d <ℝ Q
    PdQ = <-+mono-reflect {x = Q} {y = P -ℝ embedℚ d} {z = embedℚ d} shifted

    Q<Pd : Q <ℝ P +ℝ embedℚ d
    Q<Pd = ≈-<-resp Y≈Q
             (≈-<-respʳ (+ℝ-cong X≈P (≈ℝ-refl {embedℚ d})) c2)
  in
    PdQ , Q<Pd

------------------------------------------------------------------------
-- Two-sided window squeeze at real level
--
-- 实数层的双边窗户夹逼

-- If two nonnegative reals both sit inside the rational window
-- `[embed p, embed (p+h)]`, their exponential values differ by at most
-- `h*(1+B)+e`, where `B` bounds the partial sums at the right endpoint
-- The left component uses `exp x ≤ exp (p+h) < exp p + d ≤ exp y + d`;
-- the right component is the direct upper estimate
-- `exp y ≤ exp (p+h) < exp p + d ≤ exp x + d`.
--
-- 若两个非负实数都落在有理窗 `[embed p, embed (p+h)]` 内，则指数值
-- 相差不超过 `h*(1+B)+e`，其中 B 界住右端点处的部分和。左分量用
-- exp x ≤ exp (p+h) < exp p + d ≤ exp y + d；右分量直接用上界
-- 右式为 exp y ≤ exp (p+h) < exp p + d ≤ exp x + d。
expℝ-close-window : (p h : ℚ) (0≤p : 0ℚ ≤ p) (0≤h : 0ℚ ≤ h) (B : ℚ)
                    (bnd : (j : ℕ) → expPartial (p + h) j ≤ B)
                    (e : ℚ) (0<e : 0ℚ < e)
                    (x y : RealI) (0≤x : 0ℝ ≤ℝ x) (0≤y : 0ℝ ≤ℝ y)
                    (px : embedℚ p ≤ℝ x) (xq : x ≤ℝ embedℚ (p + h))
                    (py : embedℚ p ≤ℝ y) (yq : y ≤ℝ embedℚ (p + h))
                  → Close (h * (1ℚ + B) + e) (expℝ x 0≤x) (expℝ y 0≤y)
expℝ-close-window p h 0≤p 0≤h B bnd e 0<e x y 0≤x 0≤y px xq py yq =
  let
    0≤ph : 0ℚ ≤ p + h
    0≤ph = ≤-trans 0≤p (le-add-right p h 0≤h)

    d : ℚ
    d = h * (1ℚ + B) + e

    A : RealI
    A = expℝ (embedℚ p) (embed-nonNeg p 0≤p)

    Z : RealI
    Z = expℝ (embedℚ (p + h)) (embed-nonNeg (p + h) 0≤ph)

    X : RealI
    X = expℝ x 0≤x

    Y : RealI
    Y = expℝ y 0≤y

    c : Close d A Z
    c = expℝ-close-rat p h 0≤p 0≤h B bnd e 0<e

    c2 : Z <ℝ A +ℝ embedℚ d
    c2 = proj₂ c

    A≤X : A ≤ℝ X
    A≤X = expℝ-mono (embedℚ p) x (embed-nonNeg p 0≤p) 0≤x px

    X≤Z : X ≤ℝ Z
    X≤Z = expℝ-mono x (embedℚ (p + h)) 0≤x (embed-nonNeg (p + h) 0≤ph) xq

    A≤Y : A ≤ℝ Y
    A≤Y = expℝ-mono (embedℚ p) y (embed-nonNeg p 0≤p) 0≤y py

    Y≤Z : Y ≤ℝ Z
    Y≤Z = expℝ-mono y (embedℚ (p + h)) 0≤y (embed-nonNeg (p + h) 0≤ph) yq

    Ad≤Xd : A +ℝ embedℚ d ≤ℝ X +ℝ embedℚ d
    Ad≤Xd = ≤ℝ-+-mono {A} {X} {embedℚ d} A≤X

    Ad≤Yd : A +ℝ embedℚ d ≤ℝ Y +ℝ embedℚ d
    Ad≤Yd = ≤ℝ-+-mono {A} {Y} {embedℚ d} A≤Y

    X<Yd : X <ℝ Y +ℝ embedℚ d
    X<Yd = <-≤ℝ-trans (≤ℝ-<trans X≤Z c2) Ad≤Yd

    Y<Xd : Y <ℝ X +ℝ embedℚ d
    Y<Xd = <-≤ℝ-trans (≤ℝ-<trans Y≤Z c2) Ad≤Xd

    shiftedX : (X -ℝ embedℚ d) +ℝ embedℚ d <ℝ Y +ℝ embedℚ d
    shiftedX = ≈-<-resp (≈ℝ-sym (sub-add-cancelℝ X (embedℚ d))) X<Yd

    left : X -ℝ embedℚ d <ℝ Y
    left = <-+mono-reflect {x = Y} {y = X -ℝ embedℚ d} {z = embedℚ d} shiftedX
  in
    left , Y<Xd
