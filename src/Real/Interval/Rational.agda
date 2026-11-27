------------------------------------------------------------------------
-- Rational lemmas for real-interval arithmetic
--
-- 实区间算术所需的有理引理
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Rational where

open import Data.Empty using (⊥-elim)
open import Data.Integer using (+_; +<+) renaming (_*_ to _*ℤ_; _<_ to _<ℤ_)
import Data.Integer.Properties as ℤP
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _^_; _∸_)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _<_ to _<ℕ_)
import Data.Nat.Properties as ℕP
open import Data.Rational using
 (ℚ; 0ℚ; 1ℚ; _⊓_; _⊔_; _+_; _-_; _*_; _<_; _≤_; 1/_; ∣_∣; fromℚᵘ; toℚᵘ
 ; NonZero; Positive) renaming (-_ to neg)
open import Data.Rational.Base using (_÷_; positive)
open import Data.Rational.Properties using
  (+-comm; +-inverseʳ; neg-distrib-+; +-mono-<-≤; ≤-refl; *-assoc; *-identityˡ
  ; *-comm; <⇒≤; <-cmp; ≤-trans; *-inverseʳ; *-identityʳ; ≤-antisym
  ; neg-antimono-≤; 0≤∣p∣; ∣-p∣≡∣p∣; *-inverseˡ; ∣p∣≡p∨∣p∣≡-p
  ; 0≤p⇒∣p∣≡p; toℚᵘ-cancel-<; toℚᵘ-fromℚᵘ; p⊓q≤p; p⊓q≤q; p≤p⊔q; p≤q⊔p
  ; p≤q⇒p⊓q≡p; p≥q⇒p⊓q≡q; p≤q⇒p⊔q≡q; p≥q⇒p⊔q≡p; ⊓-glb; ⊔-lub; ⊓-sel; ⊔-sel
  ; +-assoc; +-identityˡ; +-identityʳ; positive⁻¹; 1/pos⇒pos; pos*pos⇒pos; *-monoˡ-<-pos
  ; *-distribʳ-+; pos⇒nonZero)
open import Data.Rational.Unnormalised.Base using
  (ℚᵘ; mkℚᵘ; _≃_; *≡*; *<*) renaming (_<_ to _<ᵘ_)
open import Data.Rational.Unnormalised.Properties using (<-respˡ-≃; <-respʳ-≃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

open import Base.RationalRing using (neg-involutive; sub-add-split; swap-mid)
open import Real.Interval.Reasoning using (begin≤_; _≈⟨_⟩_; _≤⟨_⟩_; _≤∎)

------------------------------------------------------------------------
-- Positive difference
--
-- 正差

-- a < b implies 0 < b − a.
--
-- 由 a < b 得正差。
pos-diff : ∀ a b → a < b → 0ℚ < b - a
pos-diff a b a<b =
  subst (λ z → z < b - a)
        (+-inverseʳ a)
        (+-mono-<-≤ a<b (≤-refl {neg a}))

------------------------------------------------------------------------
-- Algebra of subtraction
--
-- 减法代数

-- a + (b - a) is b: the difference cancels against its minuend
-- sub-add distributes subtraction over addition; cancel-plus cancels a
-- common addend; negsub and neg-sub flip differences. plus-diff cancels
-- the difference against the addend it was taken from.
--
-- a + (b - a) 就是 b：差与被减数相消
-- sub-add 把减法分配到加法；cancel-plus 消去公共加项；negsub 与
-- neg-sub 翻转差。plus-diff 把差与其被减数相消。
plus-diff : (a b : ℚ) → a + (b - a) ≡ b
plus-diff a b =
  begin
    a + (b + neg a)   ≡⟨ sym (+-assoc a b (neg a)) ⟩
    (a + b) + neg a   ≡⟨ cong (_+ neg a) (+-comm a b) ⟩
    (b + a) + neg a   ≡⟨ +-assoc b a (neg a) ⟩
    b + (a + neg a)   ≡⟨ cong (λ z → b + z) (+-inverseʳ a) ⟩
    b + 0ℚ            ≡⟨ +-identityʳ b ⟩
    b                 ∎

-- Regrouping three summands.
--
-- 三个加项的重排。
+rearrange : (a b c : ℚ) → (a + b) + c ≡ (a + c) + b
+rearrange a b c =
  begin
    (a + b) + c  ≡⟨ +-assoc a b c ⟩
    a + (b + c)  ≡⟨ cong (λ z → a + z) (+-comm b c) ⟩
    a + (c + b)  ≡⟨ sym (+-assoc a c b) ⟩
    (a + c) + b  ∎

-- Adding then dropping the same addend.
--
-- 加上再减去同一加项。
add-then-drop : (a s : ℚ) → (a + s) - a ≡ s
add-then-drop a s =
  begin
    (a + s) - a       ≡⟨ refl ⟩
    (a + s) + neg a   ≡⟨ +-assoc a s (neg a) ⟩
    a + (s + neg a)   ≡⟨ cong (λ z → a + z) (+-comm s (neg a)) ⟩
    a + (neg a + s)   ≡⟨ sym (+-assoc a (neg a) s) ⟩
    (a + neg a) + s   ≡⟨ cong (_+ s) (+-inverseʳ a) ⟩
    0ℚ + s            ≡⟨ +-identityˡ s ⟩
    s                 ∎

sub-add : (a b c d : ℚ) → (a + b) - (c + d) ≡ (a - c) + (b - d)
sub-add a b c d = sub-add-split a c b d

------------------------------------------------------------------------
-- Cancelling a common addend
--
-- 消去公共加项

cancel-plus : ∀ x y z → (x + y) - (x + z) ≡ y - z
cancel-plus x y z = begin
  (x + y) - (x + z)
    ≡⟨ cong (λ w → (x + y) + w) (neg-distrib-+ x z) ⟩
  (x + y) + (neg x + neg z)
    ≡⟨ +-assoc x y (neg x + neg z) ⟩
  x + (y + (neg x + neg z))
    ≡⟨ cong (λ w → x + w)
            (trans (sym (+-assoc y (neg x) (neg z)))
                   (cong (λ w → w + neg z) (+-comm y (neg x)))) ⟩
  x + ((neg x + y) + neg z)
    ≡⟨ cong (λ w → x + w) (+-assoc (neg x) y (neg z)) ⟩
  x + (neg x + (y + neg z))
    ≡⟨ sym (+-assoc x (neg x) (y + neg z)) ⟩
  (x + neg x) + (y + neg z)
    ≡⟨ cong (λ w → w + (y + neg z)) (+-inverseʳ x) ⟩
  0ℚ + (y + neg z)
    ≡⟨ +-identityˡ (y + neg z) ⟩
  y + neg z
    ≡⟨ refl ⟩
  y - z
  ∎

negsub : ∀ x y → neg (x - y) ≡ y - x
negsub x y = begin
  neg (x - y)
    ≡⟨ refl ⟩
  neg (x + neg y)
    ≡⟨ neg-distrib-+ x (neg y) ⟩
  neg x + neg (neg y)
    ≡⟨ cong (λ z → neg x + z) (neg-involutive y) ⟩
  neg x + y
    ≡⟨ +-comm (neg x) y ⟩
  y + neg x
    ≡⟨ refl ⟩
  y - x
  ∎

neg-sub-neg : ∀ a b → neg a - neg b ≡ b - a
neg-sub-neg a b = begin
  neg a - neg b
    ≡⟨ refl ⟩
  neg a + neg (neg b)
    ≡⟨ cong (λ z → neg a + z) (neg-involutive b) ⟩
  neg a + b
    ≡⟨ +-comm (neg a) b ⟩
  b + neg a
    ≡⟨ refl ⟩
  b - a
  ∎

------------------------------------------------------------------------
-- Trichotomy elimination
--
-- 三歧性消去

-- From a proof of each of the three cases, build a proof of P.
--
-- 由三种情形的证明构造 P 的证明。
tri-elim : ∀ {P : Set} (a b : ℚ)
  → (a < b → P) → (a ≡ b → P) → (b < a → P) → P
tri-elim a b lt eq gt =
  case <-cmp a b of λ where
    (tri< a<b _ _) → lt a<b
    (tri≈ _ a≡b _) → eq a≡b
    (tri> _ _ b<a) → gt b<a

------------------------------------------------------------------------
-- Minimum and maximum
--
-- 最小值与最大值

min<max : ∀ a b → ¬ (a ≡ b) → a ⊓ b < a ⊔ b
min<max a b a≠b = tri-elim a b
  (λ a<b →
     subst₂ _<_
       (sym (p≤q⇒p⊓q≡p (<⇒≤ a<b)))
       (sym (p≤q⇒p⊔q≡q (<⇒≤ a<b)))
       a<b)
  (λ a≡b → ⊥-elim (a≠b a≡b))
  (λ b<a →
     subst₂ _<_
       (sym (p≥q⇒p⊓q≡q (<⇒≤ b<a)))
       (sym (p≥q⇒p⊔q≡p (<⇒≤ b<a)))
       b<a)

------------------------------------------------------------------------
-- Absolute value and magnitude bounds
--
-- 绝对值与量级界

-- The two elementary absolute-value bounds state that both r and -r
-- are at most |r|. The magnitude combines the endpoint absolute values
-- into their maximum, and mag-≤ shows that any point inside an interval
-- is bounded by that maximum.
--
-- 两条基本绝对值界给出 r 与 -r 都不超过 |r|；mag 将端点绝对值
-- 合并为上确界，mag-≤ 表明区间内任意点的绝对值不超过该上确界。
r≤|r| : ∀ r → r ≤ ∣ r ∣
r≤|r| r =
  let
    helper : ∣ r ∣ ≡ r ⊎ ∣ r ∣ ≡ neg r → r ≤ ∣ r ∣
    helper = λ where
      (inj₁ |r|≡r) → begin≤
        r      ≈⟨ sym |r|≡r ⟩
        ∣ r ∣  ≤∎
      (inj₂ |r|≡-r) →
        let
          0≤-r : 0ℚ ≤ neg r
          0≤-r = subst (λ z → 0ℚ ≤ z) |r|≡-r (0≤∣p∣ r)

          r≤0 : r ≤ 0ℚ
          r≤0 = subst (λ z → z ≤ 0ℚ) (neg-involutive r) (neg-antimono-≤ 0≤-r)
        in begin≤
          r      ≤⟨ r≤0 ⟩
          0ℚ     ≤⟨ 0≤-r ⟩
          neg r  ≈⟨ sym |r|≡-r ⟩
          ∣ r ∣  ≤∎
  in helper (∣p∣≡p∨∣p∣≡-p r)

-r≤|r| : ∀ r → neg r ≤ ∣ r ∣
-r≤|r| r = subst (λ z → neg r ≤ z) (∣-p∣≡∣p∣ r) (r≤|r| (neg r))

-- The magnitude of an interval is the maximum of its endpoint
-- absolute values.
--
-- 区间量级为其端点绝对值的最大值。
mag : ℚ → ℚ → ℚ
mag l u = ∣ l ∣ ⊔ ∣ u ∣

mag-≤ : ∀ {l u x : ℚ} → l ≤ x → x ≤ u → ∣ x ∣ ≤ mag l u
mag-≤ {l} {u} {x} l≤x x≤u =
  let
    helper : ∣ x ∣ ≡ x ⊎ ∣ x ∣ ≡ neg x → ∣ x ∣ ≤ mag l u
    helper = λ where
      (inj₁ |x|≡x) → begin≤
        ∣ x ∣          ≈⟨ |x|≡x ⟩
        x              ≤⟨ x≤u ⟩
        u              ≤⟨ r≤|r| u ⟩
        ∣ u ∣          ≤⟨ p≤q⊔p ∣ l ∣ ∣ u ∣ ⟩
        ∣ l ∣ ⊔ ∣ u ∣  ≤∎
      (inj₂ |x|≡-x) →
        let
          0≤-x : 0ℚ ≤ neg x
          0≤-x = subst (λ z → 0ℚ ≤ z) |x|≡-x (0≤∣p∣ x)

          x≤0 : x ≤ 0ℚ
          x≤0 = subst (λ z → z ≤ 0ℚ) (neg-involutive x) (neg-antimono-≤ 0≤-x)

          l≤0 : l ≤ 0ℚ
          l≤0 = ≤-trans l≤x x≤0

          0≤-l : 0ℚ ≤ neg l
          0≤-l = neg-antimono-≤ l≤0

          |l|≡-l : ∣ l ∣ ≡ neg l
          |l|≡-l = subst (λ z → z ≡ neg l) (∣-p∣≡∣p∣ l)
                      (0≤p⇒∣p∣≡p {neg l} 0≤-l)
        in begin≤
          ∣ x ∣          ≈⟨ |x|≡-x ⟩
          neg x          ≤⟨ neg-antimono-≤ l≤x ⟩
          neg l          ≈⟨ sym |l|≡-l ⟩
          ∣ l ∣          ≤⟨ p≤p⊔q ∣ l ∣ ∣ u ∣ ⟩
          ∣ l ∣ ⊔ ∣ u ∣  ≤∎
  in helper (∣p∣≡p∨∣p∣≡-p x)

------------------------------------------------------------------------
-- Fraction comparison with a general denominator
--
-- 一般分母的分数比较

0<2^t : (t : ℕ) → 0 <ℕ 2 ^ t
0<2^t zero    = s≤s z≤n
0<2^t (suc t) = ℕP.≤-trans (s≤s z≤n) (ℕP.*-monoʳ-≤ 2 (0<2^t t))

-- suc (n ∸ 1) ≡ n for n > 0.
--
-- 当 n > 0 时结论成立。
suc∸1 : {n : ℕ} → 0 <ℕ n → suc (n ∸ 1) ≡ n
suc∸1 {n} 0<n = begin
  suc (n ∸ 1)
    ≡⟨ refl ⟩
  1 +ℕ (n ∸ 1)
    ≡⟨ ℕP.+-comm 1 (n ∸ 1) ⟩
  (n ∸ 1) +ℕ 1
    ≡⟨ ℕP.m∸n+n≡m 0<n ⟩
  n
  ∎

-- The product of a successor and a power of two is positive.
--
-- 后继与二的幂的乘积为正。
0<sucd*2^t : (d t : ℕ) → 0 <ℕ suc d *ℕ 2 ^ t
0<sucd*2^t d t = ℕP.≤-trans (0<2^t t) (ℕP.m≤n*m (2 ^ t) (suc d))

-- Raw combined fraction N / (suc d * 2^t)
-- mkℚᵘ's second argument is denominator - 1, so to get denominator
-- (suc d) * 2^t we pass (suc d) * 2^t ∸ 1.
--
-- 原始组合分数
-- mkℚᵘ 的第二参数是分母减一，故传入相应的减一值。
rawComb : (N d t : ℕ) → ℚᵘ
rawComb N d t = mkℚᵘ (+ N) (suc d *ℕ 2 ^ t ∸ 1)

-- Raw right-hand side 1/(suc k)
-- mkℚᵘ (+ 1) k has denominator suc k, hence value 1/(suc k).
--
-- 原始右端
-- mkℚᵘ (+ 1) k 的分母为 suc k。
rawR : (k : ℕ) → ℚᵘ
rawR k = mkℚᵘ (+ 1) k

combFrac : (N d t : ℕ) → ℚ
combFrac N d t = fromℚᵘ (rawComb N d t)

flip-≃ : {a b : ℚᵘ} → _≃_ a b → _≃_ b a
flip-≃ (*≡* e) = *≡* (sym e)

-- Cross-multiplication, general version.
--
-- 交叉乘法，一般版本。
rawCross : (N d k t : ℕ) →
  N *ℕ suc k <ℕ suc d *ℕ 2 ^ t →
  (+ N) *ℤ (+ suc k) <ℤ (+ 1) *ℤ (+ suc (suc d *ℕ 2 ^ t ∸ 1))
rawCross N d k t h =
  let dd    = suc d *ℕ 2 ^ t ∸ 1
      dd-eq : suc dd ≡ suc d *ℕ 2 ^ t
      dd-eq = suc∸1 (0<sucd*2^t d t)
  in
  ℤP.<-≤-trans
    (ℤP.≤-<-trans
       (ℤP.≤-reflexive (ℤP.+◃n≡+n (N *ℕ suc k)))
       (ℤP.<-≤-trans
          (+<+ h)
          (ℤP.≤-reflexive (cong +_ (sym dd-eq)))))
    (ℤP.≤-reflexive (sym (ℤP.*-identityˡ (+ suc dd))))

-- If N * (k+1) < (suc d) * 2^t then N / (suc d * 2^t) < 1/(k+1).
--
-- 若整数交叉相乘条件成立，则分数不等式成立。
comb-strict : (N d k t : ℕ) →
  N *ℕ suc k <ℕ suc d *ℕ 2 ^ t →
  combFrac N d t < fromℚᵘ (rawR k)
comb-strict N d k t h =
  toℚᵘ-cancel-<
    (let eqL : _≃_ (toℚᵘ (combFrac N d t)) (rawComb N d t)
         eqL = toℚᵘ-fromℚᵘ (rawComb N d t)
         eqR : _≃_ (toℚᵘ (fromℚᵘ (rawR k))) (rawR k)
         eqR = toℚᵘ-fromℚᵘ (rawR k)
         cross : _<ᵘ_ (rawComb N d t) (rawR k)
         cross = *<* (rawCross N d k t h)
         p1 : _<ᵘ_ (toℚᵘ (combFrac N d t)) (rawR k)
         p1 = <-respˡ-≃ (flip-≃ eqL) cross
         p2 : _<ᵘ_ (toℚᵘ (combFrac N d t))
                     (toℚᵘ (fromℚᵘ (rawR k)))
         p2 = <-respʳ-≃ (flip-≃ eqR) p1
     in p2)

------------------------------------------------------------------------
-- Reciprocal of a product
--
-- 乘积的倒数

-- The reciprocal of a product is the product of the reciprocals.
--
-- 乘积的倒数等于两因子倒数之积。
recip-*-hom : (a b : ℚ) ⦃ na : NonZero a ⦄ ⦃ nb : NonZero b ⦄
  ⦃ nab : NonZero (a * b) ⦄ →
  (1/_) (a * b) ≡ (1/_) a * (1/_) b
recip-*-hom a b ⦃ na ⦄ ⦃ nb ⦄ ⦃ nab ⦄ =
  let ia = (1/_) a
      ib = (1/_) b
      x = ia * ib
      p : x * (a * b) ≡ 1ℚ
      p =
        begin (ia * ib) * (a * b)
          ≡⟨ *-assoc ia ib (a * b) ⟩
        ia * (ib * (a * b))
          ≡⟨ cong (ia *_) (sym (*-assoc ib a b)) ⟩
        ia * ((ib * a) * b)
          ≡⟨ cong (ia *_) (cong (λ z → z * b) (*-comm ib a)) ⟩
        ia * ((a * ib) * b)
          ≡⟨ cong (ia *_) (*-assoc a ib b) ⟩
        ia * (a * (ib * b))
          ≡⟨ sym (*-assoc ia a (ib * b)) ⟩
        (ia * a) * (ib * b)
          ≡⟨ cong₂ (λ u v → u * v) (*-inverseˡ a) (*-inverseˡ b) ⟩
        1ℚ ∎
      q : x ≡ (1/_) (a * b)
      q =
        begin x
          ≡⟨ sym (*-identityʳ x) ⟩
        x * 1ℚ
          ≡⟨ cong (x *_) (sym (*-inverseʳ (a * b) ⦃ nab ⦄)) ⟩
        x * ((a * b) * (1/_) (a * b))
          ≡⟨ sym (*-assoc x (a * b) ((1/_) (a * b))) ⟩
        (x * (a * b)) * (1/_) (a * b)
          ≡⟨ cong (λ z → z * (1/_) (a * b)) p ⟩
        1ℚ * (1/_) (a * b)
          ≡⟨ *-identityˡ ((1/_) (a * b)) ⟩
        (1/_) (a * b) ∎
  in sym q

------------------------------------------------------------------------
-- Negation of min/max
--
-- 取负下的 min/max

min-neg : ∀ a b → (neg a) ⊓ (neg b) ≡ neg (a ⊔ b)
min-neg a b = ≤-antisym upper lower
  where
    lower : neg (a ⊔ b) ≤ (neg a) ⊓ (neg b)
    lower = ⊓-glb (neg-antimono-≤ (p≤p⊔q a b))
                  (neg-antimono-≤ (p≤q⊔p a b))

    upper : (neg a) ⊓ (neg b) ≤ neg (a ⊔ b)
    upper =
      let
        helper : a ⊔ b ≡ a ⊎ a ⊔ b ≡ b → (neg a) ⊓ (neg b) ≤ neg (a ⊔ b)
        helper = λ where
          (inj₁ max≡a) → begin≤
            (neg a) ⊓ (neg b)  ≤⟨ p⊓q≤p (neg a) (neg b) ⟩
            neg a              ≈⟨ cong neg (sym max≡a) ⟩
            neg (a ⊔ b)        ≤∎
          (inj₂ max≡b) → begin≤
            (neg a) ⊓ (neg b)  ≤⟨ p⊓q≤q (neg a) (neg b) ⟩
            neg b              ≈⟨ cong neg (sym max≡b) ⟩
            neg (a ⊔ b)        ≤∎
      in helper (⊔-sel a b)

max-neg : ∀ a b → (neg a) ⊔ (neg b) ≡ neg (a ⊓ b)
max-neg a b = ≤-antisym upper lower
  where
    upper : (neg a) ⊔ (neg b) ≤ neg (a ⊓ b)
    upper = ⊔-lub (neg-antimono-≤ (p⊓q≤p a b))
                  (neg-antimono-≤ (p⊓q≤q a b))

    lower : neg (a ⊓ b) ≤ (neg a) ⊔ (neg b)
    lower =
      let
        helper : a ⊓ b ≡ a ⊎ a ⊓ b ≡ b → neg (a ⊓ b) ≤ (neg a) ⊔ (neg b)
        helper = λ where
          (inj₁ min≡a) → begin≤
            neg (a ⊓ b)        ≈⟨ cong neg min≡a ⟩
            neg a              ≤⟨ p≤p⊔q (neg a) (neg b) ⟩
            (neg a) ⊔ (neg b)  ≤∎
          (inj₂ min≡b) → begin≤
            neg (a ⊓ b)        ≈⟨ cong neg min≡b ⟩
            neg b              ≤⟨ p≤q⊔p (neg a) (neg b) ⟩
            (neg a) ⊔ (neg b)  ≤∎
      in helper (⊓-sel a b)

------------------------------------------------------------------------
-- Division and the order of products
--
-- 除法与乘积的序

-- Locatedness of the exponential cut has to drive a product
-- h * (1 + B₀) below a fixed positive rational. Two ingredients are
-- needed: cancelling _÷_ against its divisor, and getting positivity and
-- strict monotonicity for products whose factors are abstract terms. The
-- stdlib positivity predicates are shaped on canonical proofs, so every
-- factor that carries one here is an embedding of a natural number, and
-- the predicates are taken as instances rather than rebuilt.
--
-- 指数割的定位性要把乘积 h*(1+B₀) 压到一个固定的正有理数之下。需要两件：
-- 把 _÷_ 与其除数相消，以及在因子为抽象项时拿到乘积的正性与严格单调
-- stdlib 的正性谓词建立在规范形状的证明上，所以这里带正性的因子一律取
-- 自然数嵌入，谓词以实例传入而不现场重建。
÷-cancel : ∀ a d → {{_ : NonZero d}} → (a ÷ d) * d ≡ a
÷-cancel a d =
  begin
    (a * (1/ d)) * d  ≡⟨ *-assoc a (1/ d) d ⟩
    a * ((1/ d) * d)  ≡⟨ cong (a *_) (*-inverseˡ d) ⟩
    a * 1ℚ            ≡⟨ *-identityʳ a ⟩
    a                 ∎

-- The quotient is the product with the reciprocal by definition, so the
-- statement below is phrased on that product; writing it with `_÷_` would
-- fix a different `NonZero` argument than the one `1/pos⇒pos` produces.
--
-- 商按定义就是与该倒数的乘积，所以下述命题直接写在这个乘积上；若用 _÷_ 写，
-- 会钉住一个与 1/pos⇒pos 产出的不同的 NonZero 参数。
÷-pos : ∀ a d → {{_ : Positive d}} → 0ℚ < a
     → 0ℚ < a * (1/_ d {{pos⇒nonZero d}})
÷-pos a d a>0 =
  positive⁻¹ (a * (1/_ d {{pos⇒nonZero d}}))
    {{pos*pos⇒pos a {{positive a>0}} (1/_ d {{pos⇒nonZero d}}) {{1/pos⇒pos d}}}}

*-<-mono-right : ∀ a b c → a < b → 0ℚ < c → a * c < b * c
*-<-mono-right a b c a<b 0<c = *-monoˡ-<-pos c {{positive 0<c}} a<b

------------------------------------------------------------------------
-- Slack for two quotients
--
-- 两个商的松弛

-- Locatedness needs d + d < q - p for the tolerance d = (q - p) / dv,
-- where dv is a natural embedding above two. The estimate reduces to
-- (1/dv) + (1/dv) < 1, which follows from 2 < dv by multiplying with the
-- positive reciprocal.
--
-- 定位性需要容差 d = (q - p) / dv 满足 d + d < q - p，其中 dv 是大于二的
-- 自然数嵌入。该估计归结为 (1/dv) + (1/dv) < 1，由 2 < dv 乘以正倒数得到。
double : (x : ℚ) → (1ℚ + 1ℚ) * x ≡ x + x
double x =
  begin
    (1ℚ + 1ℚ) * x    ≡⟨ *-distribʳ-+ x 1ℚ 1ℚ ⟩
    1ℚ * x + 1ℚ * x  ≡⟨ cong₂ _+_ (*-identityˡ x) (*-identityˡ x) ⟩
    x + x            ∎

recip-add-lt-one : (d : ℚ) → ⦃ pd : Positive d ⦄ → (1ℚ + 1ℚ) < d
                 → (1/_ d {{pos⇒nonZero d}}) + (1/_ d {{pos⇒nonZero d}}) < 1ℚ
recip-add-lt-one d {{pd}} 2<d =
  let
    r : ℚ
    r = 1/_ d {{pos⇒nonZero d}}

    0<r : 0ℚ < r
    0<r = positive⁻¹ r {{1/pos⇒pos d {{pd}}}}

    stepped : (1ℚ + 1ℚ) * r < d * r
    stepped = *-<-mono-right (1ℚ + 1ℚ) d r 2<d 0<r

    dr≡1 : d * r ≡ 1ℚ
    dr≡1 = trans (*-comm d r) (*-inverseˡ d {{pos⇒nonZero d}})
  in
    subst (λ z → r + r < z) dr≡1
      (subst (λ z → z < d * r) (double r) stepped)

------------------------------------------------------------------------
-- The reciprocal reverses strict comparisons, and undoes itself
--
-- 倒数反转严格比较，并且自逆

-- 0 < a < b implies 1/b < 1/a
-- Both statements are about positive rationals only, so the positivity
-- evidence is the argument that fixes the NonZero instance of the
-- reciprocal throughout; writing 1/_ x {{pos⇒nonZero x}} keeps that
-- instance literally the same term as the one inside 1/pos⇒pos and
-- *-inverseˡ/ʳ, which is what the two subst steps compare.
--
-- 由 0 < a < b 得 1/b < 1/a
-- 两条命题只涉及正有理数，故以正性证据作为钉住倒数 NonZero 实例的自变量；
-- 一律写 1/_ x {{pos⇒nonZero x}}，可让该实例与 1/pos⇒pos 及 *-inverseˡ/ʳ
-- 内部的实例是同一段文本，这正是两处 subst 所比较的东西。
recip-lt-of-lt : (a b : ℚ) → ⦃ pa : Positive a ⦄ → ⦃ pb : Positive b ⦄
               → a < b → 1/_ b {{pos⇒nonZero b}} < 1/_ a {{pos⇒nonZero a}}
recip-lt-of-lt a b a<b =
  let
    r-a : ℚ
    r-a = 1/_ a {{pos⇒nonZero a}}

    r-b : ℚ
    r-b = 1/_ b {{pos⇒nonZero b}}

    0<r-a : 0ℚ < r-a
    0<r-a = positive⁻¹ r-a {{1/pos⇒pos a}}

    0<r-b : 0ℚ < r-b
    0<r-b = positive⁻¹ r-b {{1/pos⇒pos b}}

    -- Multiply `a < b` by the positive reciprocal of `a`.
    --
    -- 把 `a < b` 乘以 `a` 的正倒数。
    step1 : a * r-a < b * r-a
    step1 = *-<-mono-right a b r-a a<b 0<r-a

    step1' : 1ℚ < b * r-a
    step1' = subst (λ z → z < b * r-a) (*-inverseʳ a {{pos⇒nonZero a}}) step1

    step1'' : 1ℚ < r-a * b
    step1'' = subst (λ z → 1ℚ < z) (sym (*-comm r-a b)) step1'

    -- Then multiply that by the positive reciprocal of `b`.
    --
    -- 再把它乘以 `b` 的正倒数。
    step2 : 1ℚ * r-b < (r-a * b) * r-b
    step2 = *-<-mono-right 1ℚ (r-a * b) r-b step1'' 0<r-b

    step2' : r-b < (r-a * b) * r-b
    step2' = subst (λ z → z < (r-a * b) * r-b) (*-identityˡ r-b) step2

    right-eq : (r-a * b) * r-b ≡ r-a
    right-eq =
      trans (*-assoc r-a b r-b)
        (trans (cong (r-a *_) (*-inverseʳ b {{pos⇒nonZero b}})) (*-identityʳ r-a))
  in
    subst (λ z → r-b < z) right-eq step2'
------------------------------------------------------------------------
-- Multiplication and addition of quotients
--
-- 商的乘法与加法

-- Numerator multiplies numerator and denominator multiplies denominator.
--
-- 分子与分子相乘，分母与分母相乘。
÷-mul : (a b c d : ℚ) ⦃ nb : NonZero b ⦄ ⦃ nd : NonZero d ⦄
        ⦃ nbd : NonZero (b * d) ⦄
      → (a ÷ b) * (c ÷ d) ≡ (a * c) ÷ (b * d)
÷-mul a b c d ⦃ nb ⦄ ⦃ nd ⦄ ⦃ nbd ⦄ = begin
  (a ÷ b) * (c ÷ d)
    ≡⟨ swap-mid a (1/ b) c (1/ d) ⟩
  (a * c) * ((1/ b) * (1/ d))
    ≡⟨ cong ((a * c) *_) (sym (recip-*-hom b d)) ⟩
  (a * c) * (1/ (b * d))
    ≡⟨⟩
  (a * c) ÷ (b * d) ∎

-- A common denominator distributes over a sum.
--
-- 同分母的商对和分配。
÷-distribʳ-+ : (a b c : ℚ) ⦃ nc : NonZero c ⦄
             → (a + b) ÷ c ≡ (a ÷ c) + (b ÷ c)
÷-distribʳ-+ a b c = *-distribʳ-+ (1/ c) a b
------------------------------------------------------------------------
-- Powers in ℚ
--
-- ℚ 的幂

-- Iterated multiplication with the exponent on the right.
--
-- 指数在右的反复乘法。
powQ : ℚ → ℕ → ℚ
powQ q zero    = 1ℚ
powQ q (suc k) = q * powQ q k

-- One unfolding of the recursion.
--
-- 递推的一次展开。
powQ-suc : (q : ℚ) (k : ℕ) → powQ q (suc k) ≡ q * powQ q k
powQ-suc q k = refl
