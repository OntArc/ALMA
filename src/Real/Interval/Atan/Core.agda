------------------------------------------------------------------------
-- Atan: the arctangent series at the rational level
--
-- Atan：反正切级数的有理层
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Atan.Core where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
import Data.Nat.Base as NB
import Data.Nat.Properties as NP
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_; _*_; _-_; ∣_∣)
  renaming (-_ to neg)
open import Data.Rational.Base using (1/_; NonZero; positive)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; ≤-<-trans; <⇒≤; *-assoc; *-identityˡ
  ; *-identityʳ; *-zeroˡ; *-zeroʳ; *-distribˡ-+; +-identityˡ; +-identityʳ
  ; +-assoc; +-comm; +-mono-≤; +-monoʳ-≤; +-inverseˡ; 0≤p⇒∣p∣≡p
  ; ∣-p∣≡∣p∣; ∣p*q∣≡∣p∣*∣q∣; neg-distribˡ-*; neg-antimono-≤
  ; neg-antimono-<; <-asym; pos⇒nonZero; 1/pos⇒pos; positive⁻¹)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using
  (0≤1; 0<1; neg-involutive; neg-0; neg-sub; sub-sum-swap)
open import Real using (embed; 0<embed; embed-mono-≤; embed-mono-<; ε; CauchySeq)
open import Real.CauchyToInterval using (cauchy→realI)
open import Real.Interval using (RealI)
open import Real.Interval.Series.Bounds using (le-self-add)
open import Real.Interval.Kit using
  (*-mono-≤-nonNeg; recip-antitone; strict-recip; 0≤diff)

------------------------------------------------------------------------
-- Powers of a rational
--
-- 有理数的幂

-- The arctangent of a rational q in [0,1] is the alternating series
--     atan q = Σ_k (-1)^k q^(2k+1) / (2k+1)
-- and this module defines its terms together with the three properties
-- every later slice consumes: non-negativity, decrease, and the explicit
-- bound atanTerm q n ≤ 1/(2n+1).
-- Two conventions are deliberate. The sign is carried by `sign`, whose
-- step is definitional (sign (suc n) ≡ - sign n), so that a pairing
-- argument never has to unfold a power of -1. The powers are the local
-- `qpow`, because stdlib has no rational power at all (Data.Rational
-- exposes only +, -, *, reciprocal and division); `qpow` carries the
-- laws used below, and is meant to move to a rational-power module once
-- a second caller appears.
--     atan q = Σ_k (-1)^k q^(2k+1) / (2k+1)
-- Status. qpow / idx / atanTerm together with the three term laws
-- (non-negativity, decrease, the bound atanTerm q n ≤ atanInv n),
-- sign / sign-eq / sign-abs / sign-add, altSum with its two-sided bound
-- AltInfo, the shift identity
--     altSum a (n + d) ≡ altSum a n + sign n * altSum (a ∘ (n +_)) d,
-- the shifted tail estimate |altSum a (n + d) - altSum a n| ≤ a n,
-- and atanSeq : (q) (0≤q) (q≤1) → CauchySeq with modulus suc k (the
-- tail bound is below ε k because 1/(2k+3) < 1/(k+1)), and
-- atanq : (q) (0≤q) (q≤1) → RealI (one application of cauchy→realI)
-- are proved. Not yet in this module: the real-order facts atanq-zero,
-- atanq-nonNeg and atanq ≤ q; they belong to the real-order layer and
-- are the next slice.
-- The only powers needed are odd ones of a base in [0,1], but the
-- definition is the general one: x^0 = 1, x^(n+1) = x^n * x. Its
-- recursive step is definitional, which keeps every later rewriting to a
-- single unfolding.
--
-- [0,1] 内有理数 q 的反正切是交错级数
-- 本模块定义其通项，并给出后续每个切片都要用的三条性质：非负、递减、
-- 以及显式上界 atanTerm q n ≤ 1/(2n+1)。
-- 两处约定是有意的。符号由 `sign` 携带，其步进是定义性等式
-- （sign (suc n) ≡ - sign n），于是配对论证从不需要展开 -1 的幂。
-- 幂用局部的 `qpow`，因为 stdlib 完全没有有理幂（Data.Rational 只提供
-- +、-、*、倒数与除法）；`qpow` 携带下文用到的律，等出现第二个
-- 调用者时再上提为有理幂模块。
-- 状态：qpow / idx / atanTerm 与通项三律（非负、递减、界
-- atanTerm q n ≤ atanInv n）、sign / sign-eq / sign-abs / sign-add、
-- altSum 及其双边界 AltInfo、平移恒等式
--     altSum a (n + d) ≡ altSum a n + sign n * altSum (a ∘ (n +_)) d、
-- 平移尾差估计 |altSum a (n + d) - altSum a n| ≤ a n、
-- atanSeq : (q) (0≤q) (q≤1) → CauchySeq（模数 suc k，因
-- 1/(2k+3) < 1/(k+1) 而尾界低于 ε k），以及
-- atanq : (q) (0≤q) (q≤1) → RealI（一次 cauchy→realI 调用）均已证。
-- 本模块尚未写入：实数序性质 atanq-zero、atanq-nonNeg、atanq ≤ q；
-- 它们属于实数序层，是下一个切片。
-- 需要的只是 [0,1] 内底数的奇次幂，但定义取一般形式：
-- x^0 = 1，x^(n+1) = x^n * x。其递推步是定义性的，这使后续每次改写
-- 都只需一次展开。
qpow : ℚ → ℕ → ℚ
qpow x zero    = 1ℚ
qpow x (suc n) = qpow x n * x

qpow-zero : (x : ℚ) → qpow x 0 ≡ 1ℚ
qpow-zero x = refl

qpow-suc : (x : ℚ) (n : ℕ) → qpow x (suc n) ≡ qpow x n * x
qpow-suc x n = refl

qpow-nonNeg : (x : ℚ) → 0ℚ ≤ x → (n : ℕ) → 0ℚ ≤ qpow x n
qpow-nonNeg x 0≤x zero    = 0≤1
qpow-nonNeg x 0≤x (suc n) =
  subst (λ z → z ≤ qpow x n * x) (*-zeroˡ x)
    (*-mono-≤-nonNeg {a = 0ℚ} {a' = qpow x n} {b = x} {b' = x}
      (≤-refl {0ℚ}) (qpow-nonNeg x 0≤x n) 0≤x (≤-refl {x}))

qpow-le-one : (x : ℚ) → 0ℚ ≤ x → x ≤ 1ℚ → (n : ℕ) → qpow x n ≤ 1ℚ
qpow-le-one x 0≤x x≤1 zero    = ≤-refl {1ℚ}
qpow-le-one x 0≤x x≤1 (suc n) =
  subst (λ z → qpow x n * x ≤ z) (*-identityˡ 1ℚ)
    (*-mono-≤-nonNeg {a = qpow x n} {a' = 1ℚ} {b = x} {b' = 1ℚ}
      (qpow-nonNeg x 0≤x n) (qpow-le-one x 0≤x x≤1 n) 0≤x x≤1)

qpow-add : (x : ℚ) (m n : ℕ) → qpow x (m +ℕ n) ≡ qpow x m * qpow x n
qpow-add x m zero = begin
  qpow x (m +ℕ 0)          ≡⟨ cong (qpow x) (NP.+-identityʳ m) ⟩
  qpow x m                 ≡⟨ sym (*-identityʳ (qpow x m)) ⟩
  qpow x m * 1ℚ            ∎
qpow-add x m (suc n) = begin
  qpow x (m +ℕ suc n)            ≡⟨ cong (qpow x) (NP.+-suc m n) ⟩
  qpow x (suc (m +ℕ n))          ≡⟨ qpow-suc x (m +ℕ n) ⟩
  qpow x (m +ℕ n) * x            ≡⟨ cong (_* x) (qpow-add x m n) ⟩
  (qpow x m * qpow x n) * x      ≡⟨ *-assoc (qpow x m) (qpow x n) x ⟩
  qpow x m * (qpow x n * x)      ≡⟨ cong (qpow x m *_) (sym (qpow-suc x n)) ⟩
  qpow x m * qpow x (suc n)      ∎

qpow-two : (x : ℚ) → qpow x 2 ≡ x * x
qpow-two x = cong (λ z → z * x) (*-identityˡ x)

qpow-step2 : (x : ℚ) (n : ℕ) → qpow x (suc (suc n)) ≡ qpow x n * (x * x)
qpow-step2 x n = *-assoc (qpow x n) x x

qpow-dec : (x : ℚ) → 0ℚ ≤ x → x ≤ 1ℚ → (n : ℕ)
         → qpow x (suc (suc n)) ≤ qpow x n
qpow-dec x 0≤x x≤1 n =
  subst (λ z → z ≤ qpow x n) (sym (qpow-step2 x n))
    (subst (λ z → qpow x n * (x * x) ≤ z) (*-identityʳ (qpow x n))
      (*-mono-≤-nonNeg {a = qpow x n} {a' = qpow x n}
                        {b = x * x} {b' = 1ℚ}
        (qpow-nonNeg x 0≤x n) (≤-refl {qpow x n})
        (subst (λ z → z ≤ x * x) (*-zeroˡ x)
          (*-mono-≤-nonNeg {a = 0ℚ} {a' = x} {b = x} {b' = x}
            (≤-refl {0ℚ}) 0≤x 0≤x (≤-refl {x})))
        (subst (λ z → x * x ≤ z) (*-identityˡ 1ℚ)
          (*-mono-≤-nonNeg {a = x} {a' = 1ℚ} {b = x} {b' = 1ℚ}
            0≤x x≤1 0≤x x≤1))))

------------------------------------------------------------------------
-- The odd index 2n+1
--
-- 奇下标 2n+1

-- idx n = 2n+1, and idx (suc n) equals suc (suc (idx n)) by one use of
-- the successor law of addition; that is what makes the decrease
-- argument one rewrite instead of an arithmetic detour.
--
-- idx n = 2n+1，且 idx (suc n) 经一次加法后继律即等于 suc (suc (idx n))；
-- 后者让递减论证只需一次改写，而不必绕道算术。
idx : ℕ → ℕ
idx n = suc (n +ℕ n)

idx-suc : (n : ℕ) → idx (suc n) ≡ suc (suc (idx n))
idx-suc n = cong (λ k → suc k) (NP.+-suc (suc n) n)

idx-nz : (n : ℕ) → NonZero (embed (idx n))
idx-nz n = pos⇒nonZero (embed (idx n)) {{positive (0<embed (n +ℕ n))}}

idx-inc : (n : ℕ) → idx n NB.≤ idx (suc n)
idx-inc n =
  subst (λ k → idx n NB.≤ k) (sym (idx-suc n))
    (NP.≤-trans (NP.n≤1+n (idx n)) (NP.n≤1+n (suc (idx n))))

------------------------------------------------------------------------
-- Terms of the arctangent series
--
-- 反正切级数的通项

-- atanTerm q n = q^(2n+1) * (1/(2n+1)). The reciprocal is written with an
-- explicit `NonZero` witness so that no instance is ever synthesised.
--
-- atanTerm q n = q^(2n+1) * (1/(2n+1))。倒数用显式的 `NonZero` 见证
-- 书写，因此任何时候都不会合成 instance。
atanInv : ℕ → ℚ
atanInv n = 1/_ (embed (idx n)) {{idx-nz n}}

atanTerm : ℚ → ℕ → ℚ
atanTerm q n = qpow q (idx n) * atanInv n

atanInv-nonNeg : (n : ℕ) → 0ℚ ≤ atanInv n
atanInv-nonNeg n =
  <⇒≤ (positive⁻¹ (atanInv n)
    {{1/pos⇒pos (embed (idx n)) {{positive (0<embed (n +ℕ n))}}}})

atanTerm-nonNeg : (q : ℚ) (0≤q : 0ℚ ≤ q) (n : ℕ) → 0ℚ ≤ atanTerm q n
atanTerm-nonNeg q 0≤q n =
  subst (λ z → z ≤ qpow q (idx n) * atanInv n) (*-zeroˡ (atanInv n))
    (*-mono-≤-nonNeg {a = 0ℚ} {a' = qpow q (idx n)}
                      {b = atanInv n} {b' = atanInv n}
      (≤-refl {0ℚ}) (qpow-nonNeg q 0≤q (idx n))
      (atanInv-nonNeg n) (≤-refl {atanInv n}))

atanTerm-bound : (q : ℚ) (0≤q : 0ℚ ≤ q) (q≤1 : q ≤ 1ℚ) (n : ℕ)
               → atanTerm q n ≤ atanInv n
atanTerm-bound q 0≤q q≤1 n =
  subst (λ z → atanTerm q n ≤ z) (*-identityˡ (atanInv n))
    (*-mono-≤-nonNeg {a = qpow q (idx n)} {a' = 1ℚ}
                      {b = atanInv n} {b' = atanInv n}
      (qpow-nonNeg q 0≤q (idx n)) (qpow-le-one q 0≤q q≤1 (idx n))
      (atanInv-nonNeg n) (≤-refl {atanInv n}))

atanTerm-dec : (q : ℚ) (0≤q : 0ℚ ≤ q) (q≤1 : q ≤ 1ℚ) (n : ℕ)
             → atanTerm q (suc n) ≤ atanTerm q n
atanTerm-dec q 0≤q q≤1 n =
  *-mono-≤-nonNeg {a = qpow q (idx (suc n))} {a' = qpow q (idx n)}
                   {b = atanInv (suc n)} {b' = atanInv n}
    (qpow-nonNeg q 0≤q (idx (suc n)))
    (subst (λ k → qpow q k ≤ qpow q (idx n)) (sym (idx-suc n))
      (qpow-dec q 0≤q q≤1 (idx n)))
    (atanInv-nonNeg (suc n))
    (recip-antitone {a = embed (idx n)} {b = embed (idx (suc n))}
      (0<embed (n +ℕ n))
      (embed-mono-≤ {m = idx n} {n = idx (suc n)} (idx-inc n)))

------------------------------------------------------------------------
-- Alternating sums and their two-sided bound
--
-- 交错和及其双边界

-- The series' signs are produced by a local `sign`, whose only law we
-- need is that it is `1` or `-1` and that negating flips it. Both facts
-- are definitional consequences of the step `sign (suc n) = - sign n`,
-- so no parity function is introduced.
-- A partial sum is `altSum a d`, the sum of sign j * a j for j < d. Its
-- key property is that it stays inside [0, a 0] whenever `a` is non-
-- negative and decreasing; the proof needs the strengthened invariant
-- AltInfo, which records at the boundary which side of the bracket the
-- last term sits on. This is exactly the information the tail estimate
-- consumes later.
-- Two basic facts about `sign`.
--
-- 级数的符号由局部 `sign` 生成；只需两条律：取值 1 或 -1，取负即翻转。
-- 两者都是步进 sign (suc n) = - sign n 的定义性推论，因此不引入奇偶函数。
-- 部分和 altSum a d 是 sign j * a j 对 j < d 的求和。其关键性质是：只要
-- `a` 非负且递减，它就落在 [0, a 0] 内；证明需要强化不变式 AltInfo，
-- 逐层记录最后一项落在区间的哪一侧。这正是后续尾差估计要用的信息。
-- `sign` 的两条基本事实。
sign : ℕ → ℚ
sign zero    = 1ℚ
sign (suc n) = neg (sign n)

sign-eq : (n : ℕ) → (sign n ≡ 1ℚ) ⊎ (sign n ≡ neg 1ℚ)
sign-eq zero    = inj₁ refl
sign-eq (suc n) with sign-eq n
... | inj₁ e = inj₂ (cong neg e)
... | inj₂ e = inj₁ (trans (cong neg e) (neg-involutive 1ℚ))

-- 1 and -1 are distinct, so a premise that asks sign n to be both is
-- discharged by contradiction.
--
-- 1 与 -1 不同，因此同时要求 sign n 取两者的前提一律用矛盾消去。
1≢neg1 : 1ℚ ≡ neg 1ℚ → ⊥
1≢neg1 e = <-asym (subst (λ z → 0ℚ < z) e 0<1) neg1<0
  where
  neg1<0 : neg 1ℚ < 0ℚ
  neg1<0 = subst (λ z → neg 1ℚ < z) (sym neg-0)
             (neg-antimono-< {0ℚ} {1ℚ} 0<1)


------------------------------------------------------------------------
-- Partial sums of an alternating series
--
-- 交错级数的部分和

altSum : (ℕ → ℚ) → ℕ → ℚ
altSum a zero    = 0ℚ
altSum a (suc d) = altSum a d + sign d * a d

altSum-suc : (a : ℕ → ℚ) (d : ℕ)
           → altSum a (suc d) ≡ altSum a d + sign d * a d
altSum-suc a d = refl

------------------------------------------------------------------------
-- The strengthened invariant and its step
--
-- 强化不变式及其步进

-- AltInfo a d bundles four facts: the sum is non-negative, it is at most
-- a 0, and — depending on the parity of d — either the sum plus a d is
-- still below a 0, or a d alone already sits below the sum. The step
-- below splits on `sign d` through sign-eq; in each branch exactly one
-- of the two parity-dependent clauses has a false premise, discharged by
-- 1≢neg1.
--
-- AltInfo a d 捆绑四件事：和式非负、不超过 a 0，并且按 d 的奇偶，
-- 或者"和式 + a d"仍在 a 0 之下，或者 a d 本身已在和式之下。下面的步进
-- 用 sign-eq 对 `sign d` 分情况；每个分支里两条依赖奇偶的子句恰有一条
-- 前提为假，用 1≢neg1 消去。
AltInfo : (a : ℕ → ℚ) (d : ℕ) → Set
AltInfo a d =
  (0ℚ ≤ altSum a d) × (altSum a d ≤ a 0)
  × ((sign d ≡ 1ℚ) → altSum a d + a d ≤ a 0)
  × ((sign d ≡ neg 1ℚ) → a d ≤ altSum a d)

altSum-step : (a : ℕ → ℚ) (dec : ∀ n → a (suc n) ≤ a n)
              (0≤a : ∀ n → 0ℚ ≤ a n) (d : ℕ)
            → AltInfo a d → AltInfo a (suc d)
altSum-step a dec 0≤a d IH with sign-eq d
... | inj₁ e1 =
  let
    A  = proj₁ IH
    C  = proj₁ (proj₂ (proj₂ IH))
    bp = a d
    b  = a (suc d)
    step = trans (altSum-suc a d)
             (cong (λ z → altSum a d + z)
               (trans (cong (λ z → z * bp) e1) (*-identityˡ bp)))
    A' = subst (λ z → 0ℚ ≤ z) (sym step)
           (subst (λ z → z ≤ altSum a d + bp) (+-identityˡ 0ℚ)
             (+-mono-≤ {0ℚ} {altSum a d} {0ℚ} {bp} A (0≤a d)))
    B' = subst (λ z → z ≤ a 0) (sym step) (C e1)
    C' = λ e → ⊥-elim (1≢neg1 (sym (trans (sym (cong neg e1)) e)))
    D' = λ e →
           subst (λ z → b ≤ z) (sym step)
             (≤-trans (dec d)
               (subst (λ z → bp ≤ z) (+-comm bp (altSum a d))
                 (le-self-add {p = bp} {q = altSum a d} A)))
  in A' , B' , C' , D'
... | inj₂ e2 =
  let
    B  = proj₁ (proj₂ IH)
    D  = proj₂ (proj₂ (proj₂ IH))
    bp = a d
    b  = a (suc d)
    negTimes = trans (cong (λ z → z * bp) e2)
                 (trans (sym (neg-distribˡ-* 1ℚ bp))
                   (cong neg (*-identityˡ bp)))
    step = trans (altSum-suc a d) (cong (λ z → altSum a d + z) negTimes)
    negb≤0 : neg bp ≤ 0ℚ
    negb≤0 = subst (λ z → neg bp ≤ z) (sym neg-0)
               (neg-antimono-≤ {0ℚ} {bp} (0≤a d))
    subL : altSum a d + neg bp ≤ altSum a d
    subL = ≤-trans (+-monoʳ-≤ (altSum a d) negb≤0)
             (≤-reflexive (+-identityʳ (altSum a d)))
    leftEq : (altSum a d + neg bp) + bp ≤ altSum a d
    leftEq = ≤-trans
               (≤-reflexive (+-assoc (altSum a d) (neg bp) bp))
               (≤-trans
                 (+-monoʳ-≤ (altSum a d) (≤-reflexive (+-inverseˡ bp)))
                 (≤-reflexive (+-identityʳ (altSum a d))))
    leftPart : (altSum a d + neg bp) + b ≤ altSum a d
    leftPart = ≤-trans (+-monoʳ-≤ (altSum a d + neg bp) (dec d)) leftEq
    A' = subst (λ z → 0ℚ ≤ z) (sym step)
           (0≤diff {a = bp} {b = altSum a d} (D e2))
    B' = subst (λ z → z ≤ a 0) (sym step) (≤-trans subL B)
    C' = λ e → subst (λ z → z + b ≤ a 0) (sym step) (≤-trans leftPart B)
    D' = λ e → ⊥-elim (1≢neg1
           (trans (sym (trans (cong neg e2) (neg-involutive 1ℚ))) e))
  in A' , B' , C' , D'

-- The induction is structural on d; the step is kept as a separate
-- function so that the termination checker sees only `d -> suc d`.
--
-- 归纳对 d 结构进行；步进单独成函数，使终止检查只看到 `d -> suc d`。
altSum-info : (a : ℕ → ℚ) (dec : ∀ n → a (suc n) ≤ a n)
              (0≤a : ∀ n → 0ℚ ≤ a n) (d : ℕ) → AltInfo a d
altSum-info a dec 0≤a zero =
  ≤-refl {0ℚ} , 0≤a 0
  , (λ e → ≤-reflexive (+-identityˡ (a 0)))
  , (λ e → ⊥-elim (1≢neg1 e))
altSum-info a dec 0≤a (suc d) = altSum-step a dec 0≤a d (altSum-info a dec 0≤a d)

-- The bound consumed later, stated without the parity clauses.
--
-- 后续要用的界，去掉奇偶子句后即为下面的形式。
altSum-bounds : (a : ℕ → ℚ) (dec : ∀ n → a (suc n) ≤ a n)
                (0≤a : ∀ n → 0ℚ ≤ a n) (d : ℕ)
              → (0ℚ ≤ altSum a d) × (altSum a d ≤ a 0)
altSum-bounds a dec 0≤a d =
  let I = altSum-info a dec 0≤a d in proj₁ I , proj₁ (proj₂ I)

------------------------------------------------------------------------
-- The sign is multiplicative and the partial sums shift additively
--
-- 符号可乘，部分和可平移

sign-add : (m n : ℕ) → sign (m +ℕ n) ≡ sign m * sign n
sign-add zero n = sym (*-identityˡ (sign n))
sign-add (suc m) n =
  trans (cong neg (sign-add m n)) (neg-distribˡ-* (sign m) (sign n))

shift : (a : ℕ → ℚ) (n d : ℕ)
      → altSum a (n +ℕ d)
        ≡ altSum a n + sign n * altSum (λ j → a (n +ℕ j)) d
shift a n zero = begin
  altSum a (n +ℕ 0)        ≡⟨ cong (altSum a) (NP.+-identityʳ n) ⟩
  altSum a n               ≡⟨ sym (+-identityʳ (altSum a n)) ⟩
  altSum a n + 0ℚ          ≡⟨ cong (altSum a n +_) (sym (*-zeroʳ (sign n))) ⟩
  altSum a n + sign n * 0ℚ ∎

shift a n (suc d) = begin
  altSum a (n +ℕ suc d)
    ≡⟨ cong (altSum a) (NP.+-suc n d) ⟩
  altSum a (suc (n +ℕ d))
    ≡⟨ altSum-suc a (n +ℕ d) ⟩
  altSum a (n +ℕ d) + sign (n +ℕ d) * a (n +ℕ d)
    ≡⟨ cong (_+ sign (n +ℕ d) * a (n +ℕ d)) (shift a n d) ⟩
  (altSum a n + sign n * altSum (λ j → a (n +ℕ j)) d)
    + sign (n +ℕ d) * a (n +ℕ d)
    ≡⟨ cong ((altSum a n + sign n * altSum (λ j → a (n +ℕ j)) d) +_) step2 ⟩
  (altSum a n + sign n * altSum (λ j → a (n +ℕ j)) d)
    + sign n * (sign d * a (n +ℕ d))
    ≡⟨ +-assoc (altSum a n)
         (sign n * altSum (λ j → a (n +ℕ j)) d)
         (sign n * (sign d * a (n +ℕ d))) ⟩
  altSum a n + (sign n * altSum (λ j → a (n +ℕ j)) d
                + sign n * (sign d * a (n +ℕ d)))
    ≡⟨ cong (altSum a n +_)
         (sym (*-distribˡ-+ (sign n)
                (altSum (λ j → a (n +ℕ j)) d)
                (sign d * a (n +ℕ d)))) ⟩
  altSum a n + sign n * (altSum (λ j → a (n +ℕ j)) d
                        + sign d * a (n +ℕ d))  ∎
  where
  step2 : sign (n +ℕ d) * a (n +ℕ d) ≡ sign n * (sign d * a (n +ℕ d))
  step2 = begin
    sign (n +ℕ d) * a (n +ℕ d)   ≡⟨ cong (_* a (n +ℕ d)) (sign-add n d) ⟩
    (sign n * sign d) * a (n +ℕ d) ≡⟨ *-assoc (sign n) (sign d) (a (n +ℕ d)) ⟩
    sign n * (sign d * a (n +ℕ d)) ∎

------------------------------------------------------------------------
-- The tail of the alternating sum is bounded by its first term
--
-- 交错和尾段由其首项界定

one-abs : ∣ 1ℚ ∣ ≡ 1ℚ
one-abs = 0≤p⇒∣p∣≡p {1ℚ} 0≤1

sign-abs : (n : ℕ) → ∣ sign n ∣ ≡ 1ℚ
sign-abs n with sign-eq n
... | inj₁ e = subst (λ z → ∣ z ∣ ≡ 1ℚ) (sym e) one-abs
... | inj₂ e = subst (λ z → ∣ z ∣ ≡ 1ℚ) (sym e)
                 (trans (∣-p∣≡∣p∣ 1ℚ) one-abs)

altSum-tail : (a : ℕ → ℚ) (dec : ∀ k → a (suc k) ≤ a k)
              (0≤a : ∀ k → 0ℚ ≤ a k) (n d : ℕ)
            → ∣ altSum a (n +ℕ d) - altSum a n ∣ ≤ a n
altSum-tail a dec 0≤a n d =
  let
    dec' : ∀ j → a (n +ℕ suc j) ≤ a (n +ℕ j)
    dec' j = subst (λ z → a z ≤ a (n +ℕ j)) (sym (NP.+-suc n j)) (dec (n +ℕ j))
    I : (0ℚ ≤ altSum (λ j → a (n +ℕ j)) d)
        × (altSum (λ j → a (n +ℕ j)) d ≤ a (n +ℕ 0))
    I = altSum-bounds (λ j → a (n +ℕ j)) dec' (λ j → 0≤a (n +ℕ j)) d
    tailEq : altSum a (n +ℕ d) - altSum a n
             ≡ sign n * altSum (λ j → a (n +ℕ j)) d
    tailEq = trans (cong (λ z → z - altSum a n) (shift a n d))
              (sub-sum-swap (altSum a n)
                (sign n * altSum (λ j → a (n +ℕ j)) d))
    absEq : ∣ altSum a (n +ℕ d) - altSum a n ∣
            ≡ altSum (λ j → a (n +ℕ j)) d
    absEq = trans (cong ∣_∣ tailEq)
              (trans (∣p*q∣≡∣p∣*∣q∣ (sign n) (altSum (λ j → a (n +ℕ j)) d))
                (trans (cong (_* ∣ altSum (λ j → a (n +ℕ j)) d ∣) (sign-abs n))
                  (trans (*-identityˡ ∣ altSum (λ j → a (n +ℕ j)) d ∣)
                    (0≤p⇒∣p∣≡p (proj₁ I)))))
    bound : altSum (λ j → a (n +ℕ j)) d ≤ a n
    bound = subst (λ z → altSum (λ j → a (n +ℕ j)) d ≤ z)
              (cong (λ k → a k) (NP.+-identityʳ n)) (proj₂ I)
  in subst (λ z → z ≤ a n) (sym absEq) bound

------------------------------------------------------------------------
-- The atangent partial sums are Cauchy, with an explicit modulus
--
-- 反正切部分和是柯西列，且模数显式

-- The tail estimate compares any two positions once we know which one
-- comes first. On ℕ that order is decided by ≤-total, and the larger
-- index is written as the smaller one plus (larger ∸ smaller), which is
-- exactly the shape `altSum-tail` consumes; the transport happens on the
-- *values* of altSum (via cong) rather than on the index, so no motive
-- ever mentions a call-term applied to a variable.
-- The modulus is suc k. Since ε k = 1/(k+1) while atanInv (suc k) =
-- 1/(2k+3), the reciprocal is strictly antitone, so the tail bound a n
-- is below ε k as soon as n ≥ suc k.
--
-- 只要知道两个位置谁在前，尾差估计就能比较任意两项。ℕ 上的这个次序由
-- ≤-total 判定，而较大指标写成"较小指标 + (大 ∸ 小)"，正是 `altSum-tail`
-- 需要的形状；搬移发生在 altSum 的*值*上（经 cong），而不是在指标上，
-- 于是没有任何 motive 提及以变量为实参的 call-term。
-- 模数取 suc k。因为 ε k = 1/(k+1) 而 atanInv (suc k) = 1/(2k+3)，
-- 倒数严格反单调，所以只要 n ≥ suc k，尾界 a n 就低于 ε k。
atanInv-lt-ε : (k n : ℕ) → suc k NB.≤ n → atanInv n < ε k
atanInv-lt-ε k n k≤n =
  let
    hLt : suc k NB.< idx n
    hLt = NP.≤-trans (NB.s≤s k≤n) (NB.s≤s (NP.m≤m+n n n))
  in strict-recip (embed (suc k)) (embed (idx n)) (0<embed k)
       (embed-mono-< hLt)

atan-pair : (q : ℚ) (0≤q : 0ℚ ≤ q) (q≤1 : q ≤ 1ℚ) (k n m : ℕ)
          → suc k NB.≤ n → suc k NB.≤ m
          → ∣ altSum (atanTerm q) n - altSum (atanTerm q) m ∣ < ε k
atan-pair q 0≤q q≤1 k n m n≥ m≥ with NP.≤-total n m
... | inj₁ n≤m =
  let
    e : n +ℕ (m ∸ n) ≡ m
    e = NP.m+[n∸m]≡n {n} {m} n≤m
    tail : ∣ altSum (atanTerm q) (n +ℕ (m ∸ n)) - altSum (atanTerm q) n ∣
           ≤ atanTerm q n
    tail = altSum-tail (atanTerm q) (atanTerm-dec q 0≤q q≤1)
             (atanTerm-nonNeg q 0≤q) n (m ∸ n)
    atM : ∣ altSum (atanTerm q) m - altSum (atanTerm q) n ∣ ≤ atanTerm q n
    atM = subst (λ z → ∣ z - altSum (atanTerm q) n ∣ ≤ atanTerm q n)
            (cong (altSum (atanTerm q)) e) tail
    left : ∣ altSum (atanTerm q) m - altSum (atanTerm q) n ∣ < ε k
    left = ≤-<-trans atM
             (≤-<-trans (atanTerm-bound q 0≤q q≤1 n) (atanInv-lt-ε k n n≥))
    absEq : ∣ altSum (atanTerm q) m - altSum (atanTerm q) n ∣
            ≡ ∣ altSum (atanTerm q) n - altSum (atanTerm q) m ∣
    absEq = trans
              (cong ∣_∣
                (sym (neg-sub (altSum (atanTerm q) n) (altSum (atanTerm q) m))))
              (∣-p∣≡∣p∣ (altSum (atanTerm q) n - altSum (atanTerm q) m))
  in subst (λ z → z < ε k) absEq left
... | inj₂ m≤n =
  let
    e : m +ℕ (n ∸ m) ≡ n
    e = NP.m+[n∸m]≡n {m} {n} m≤n
    tail : ∣ altSum (atanTerm q) (m +ℕ (n ∸ m)) - altSum (atanTerm q) m ∣
           ≤ atanTerm q m
    tail = altSum-tail (atanTerm q) (atanTerm-dec q 0≤q q≤1)
             (atanTerm-nonNeg q 0≤q) m (n ∸ m)
  in ≤-<-trans
       (subst (λ z → ∣ z - altSum (atanTerm q) m ∣ ≤ atanTerm q m)
              (cong (altSum (atanTerm q)) e) tail)
       (≤-<-trans (atanTerm-bound q 0≤q q≤1 m) (atanInv-lt-ε k m m≥))

atan-cauchy : (q : ℚ) (0≤q : 0ℚ ≤ q) (q≤1 : q ≤ 1ℚ) (k : ℕ)
            → Σ ℕ (λ N → ∀ n m → N NB.≤ n → N NB.≤ m
                          → ∣ altSum (atanTerm q) n - altSum (atanTerm q) m ∣
                            < ε k)
atan-cauchy q 0≤q q≤1 k =
  suc k , λ n m n≥ m≥ → atan-pair q 0≤q q≤1 k n m n≥ m≥

atanSeq : (q : ℚ) (0≤q : 0ℚ ≤ q) (q≤1 : q ≤ 1ℚ) → CauchySeq
atanSeq q 0≤q q≤1 = record
  { f      = λ n → altSum (atanTerm q) n
  ; μ      = λ k → suc k
  ; cauchy = λ k n m n≥ m≥ → atan-pair q 0≤q q≤1 k n m n≥ m≥
  }

------------------------------------------------------------------------
-- atan as a real interval
--
-- 反正切的实区间

-- The completion bridge turns the Cauchy sequence of partial sums into a
-- RealI; nothing else is needed at this layer, because the sequence of
-- rationals is itself the object that cauchy→realI rebuilds intervals
-- from. The argument hypotheses stay explicit so that no work is done
-- here that belongs to the real-order layer.
--
-- 完备性桥把部分和柯西列变成 RealI；这一层不需要别的，因为有部分和
-- 有理序列本身就是 cauchy→realI 重建区间所用的对象。参数假设保持显式，
-- 以免在本层做本属于实数序层的工作。
atanq : (q : ℚ) (0≤q : 0ℚ ≤ q) (q≤1 : q ≤ 1ℚ) → RealI
atanq q 0≤q q≤1 = cauchy→realI (atanSeq q 0≤q q≤1)

------------------------------------------------------------------------
-- The first series term is q itself
--
-- 级数首项即 q

-- qpow q 1 is definitionally 1ℚ * q and atanInv 0 is definitionally
-- 1ℚ, so two identity laws close the equation. This is a statement
-- about the term layer, hence it lives at the end of Core rather than in
-- Atan/Order.
--
-- qpow q 1 定义性地等于 1ℚ * q，atanInv 0 定义性地等于 1ℚ，故两条单位律
-- 即可闭合该等式。这是关于通项层的事实，因此落在 Core 末尾而不是
-- Atan/Order。
atanTerm-zero : (q : ℚ) → atanTerm q 0 ≡ q
atanTerm-zero q = begin
  qpow q (idx 0) * atanInv 0
    ≡⟨ cong (λ z → z * atanInv 0) (*-identityˡ q) ⟩
  q * atanInv 0
    ≡⟨ *-identityʳ q ⟩
  q                         ∎
