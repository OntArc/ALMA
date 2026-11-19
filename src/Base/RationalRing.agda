------------------------------------------------------------------------
-- Shared ring-rearrangement lemmas over ℚ
--
-- ℚ 上的共享环重排引理
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Base.RationalRing where

open import Algebra.Properties.Group using (⁻¹-involutive)
open import Algebra.Properties.CommutativeMonoid using (medial)
open import Algebra.Properties.Ring using ([-x][-y]≈xy; [y-z]x≈yx-zx; x[y-z]≈xy-xz)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; -_; _<_; _≤_)
open import Data.Rational.Properties using
  (+-assoc; +-comm; +-identityˡ; +-identityʳ; +-inverseˡ; *-assoc; *-comm
  ; *-identityˡ; *-zeroˡ; *-distribˡ-+; *-distribʳ-+; neg-distrib-+; positive⁻¹
  ; neg-distribʳ-*; <⇒≤; +-0-group; +-*-ring; +-0-commutativeMonoid
  ; *-1-commutativeMonoid; +-monoˡ-<; +-monoˡ-≤; neg-antimono-<; +-inverseʳ
  ; +-monoʳ-<; <-trans)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Unit and zero constants
--
-- 单位与零常量

-- The rational unit is positive.
--
-- 有理数单位为正。
0<1 : 0ℚ < 1ℚ
0<1 = positive⁻¹ 1ℚ

-- The rational unit is nonnegative.
--
-- 有理数单位非负。
0≤1 : 0ℚ ≤ 1ℚ
0≤1 = <⇒≤ 0<1

------------------------------------------------------------------------
-- Medial laws, from the commutative-monoid structure on ℚ
--
-- medial 律，来自 ℚ 的交换幺半群结构

-- Medial law for `+`.
--
-- 加法的 medial 律。
+interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+interchange = medial +-0-commutativeMonoid

-- Medial law for `*`.
--
-- 乘法的 medial 律。
swap-mid : ∀ a b c d → (a * b) * (c * d) ≡ (a * c) * (b * d)
swap-mid = medial *-1-commutativeMonoid

------------------------------------------------------------------------
-- Negation
--
-- 取负

-- Double negation is the identity, inherited from the additive group
-- structure on ℚ.
--
-- 双重取负为恒等，继承自 ℚ 的加法群结构。
neg-involutive : ∀ x → - (- x) ≡ x
neg-involutive = ⁻¹-involutive +-0-group

-- Negating zero yields zero.
--
-- 零的取负仍是零。
neg-0 : - 0ℚ ≡ 0ℚ
neg-0 = refl

-- The product of two negations is the original product.
--
-- 两个取负相乘得到原乘积。
neg-neg-mul : ∀ x y → (- x) * (- y) ≡ x * y
neg-neg-mul = [-x][-y]≈xy +-*-ring

------------------------------------------------------------------------
-- Additive rearrangement
--
-- 加法重排

-- Reassociate a left-leaning four-term sum into right-nested form.
--
-- 将左倾的四项和重组为右结合。
flat4 : ∀ p q r s → ((p + q) + r) + s ≡ p + (q + (r + s))
flat4 p q r s = begin
  ((p + q) + r) + s
  ≡⟨ +-assoc (p + q) r s ⟩
  (p + q) + (r + s)
  ≡⟨ +-assoc p q (r + s) ⟩
  p + (q + (r + s)) ∎

-- A negated pair cancels against the corresponding positive pair.
--
-- 取负对与正对相消。
cancel-pair : ∀ t → (- t + - t) + (t + t) ≡ 0ℚ
cancel-pair t = begin
  (- t + - t) + (t + t)
  ≡⟨ cong (_+ (t + t)) (sym (neg-distrib-+ t t)) ⟩
  (- (t + t)) + (t + t)
  ≡⟨ +-inverseˡ (t + t) ⟩
  0ℚ ∎

-- Two adjacent differences combine into a single difference, with the
-- middle term cancelling.
--
-- 相邻差合并：中间项抵消。
telescope : ∀ a b c → (a + (- b)) + (b + (- c)) ≡ a + (- c)
telescope a b c = begin
  (a + (- b)) + (b + (- c))
  ≡⟨ +-assoc a (- b) (b + (- c)) ⟩
  a + ((- b) + (b + (- c)))
  ≡⟨ cong (a +_) (sym (+-assoc (- b) b (- c))) ⟩
  a + (((- b) + b) + (- c))
  ≡⟨ cong (a +_) (cong (_+ (- c)) (+-inverseˡ b)) ⟩
  a + (0ℚ + (- c))
  ≡⟨ cong (a +_) (+-identityˡ (- c)) ⟩
  a + (- c) ∎

------------------------------------------------------------------------
-- Squares
--
-- 平方

-- Square of a sum: two squares plus two cross terms.
--
-- 和之平方展开：拆成两个平方加上两个交叉项。
sq+ : ∀ x y → (x + y) * (x + y) ≡
              x * x + (y * y + (x * y + x * y))
sq+ x y = begin
  (x + y) * (x + y)
  ≡⟨ *-distribʳ-+ (x + y) x y ⟩
  x * (x + y) + y * (x + y)
  ≡⟨ cong₂ _+_ (*-distribˡ-+ x x y) (*-distribˡ-+ y x y) ⟩
  (x * x + x * y) + (y * x + y * y)
  ≡⟨ cong (λ t → (x * x + x * y) + (t + y * y)) (*-comm y x) ⟩
  (x * x + x * y) + (x * y + y * y)
  ≡⟨ +-assoc (x * x) (x * y) (x * y + y * y) ⟩
  x * x + (x * y + (x * y + y * y))
  ≡⟨ cong (x * x +_) (sym (+-assoc (x * y) (x * y) (y * y))) ⟩
  x * x + ((x * y + x * y) + y * y)
  ≡⟨ cong (x * x +_) (+-comm (x * y + x * y) (y * y)) ⟩
  x * x + (y * y + (x * y + x * y)) ∎

-- Square of a difference: as for sums, but the cross terms are negated.
--
-- 差之平方展开：与和的情形相同，交叉项取负。
sq- : ∀ x y → (x - y) * (x - y) ≡
              x * x + (y * y + (- (x * y) + - (x * y)))
sq- x y = begin
  (x - y) * (x - y)
  ≡⟨ refl ⟩
  (x + (- y)) * (x + (- y))
  ≡⟨ sq+ x (- y) ⟩
  x * x + ((- y) * (- y) + (x * (- y) + x * (- y)))
  ≡⟨ cong (x * x +_)
          (cong₂ (λ u v → u + (v + v))
                (neg-neg-mul y y)
                (sym (neg-distribʳ-* x y))) ⟩
  x * x + (y * y + (- (x * y) + - (x * y))) ∎

-- By rearranging the four factors, the two cross products are equal.
--
-- 通过重排四个因子，两个交叉乘积相等。
cross-eq : ∀ a b c d → (a * c) * (b * d) ≡ (a * d) * (b * c)
cross-eq a b c d = begin
  (a * c) * (b * d)
    ≡⟨ swap-mid a c b d ⟩
  (a * b) * (c * d)
    ≡⟨ cong ((a * b) *_) (*-comm c d) ⟩
  (a * b) * (d * c)
    ≡⟨ sym (swap-mid a d b c) ⟩
  (a * d) * (b * c) ∎

-- Swap the last two factors of a left-associated triple product.
--
-- 翻转左结合三元乘积的后两个因子。
flip3 : ∀ s x y → (s * x) * y ≡ (s * y) * x
flip3 s x y = begin
  (s * x) * y
  ≡⟨ *-assoc s x y ⟩
  s * (x * y)
  ≡⟨ cong (s *_) (*-comm x y) ⟩
  s * (y * x)
  ≡⟨ sym (*-assoc s y x) ⟩
  (s * y) * x ∎

------------------------------------------------------------------------
-- Mixed sign and subtraction
--
-- 混合符号与减法

-- Right distributivity of multiplication over subtraction.
--
-- 右乘减法的分配。
*ʳ-sub : ∀ x y z → (x - y) * z ≡ x * z - y * z
*ʳ-sub x y z = [y-z]x≈yx-zx +-*-ring z x y

-- Left distributivity of multiplication over subtraction.
--
-- 左乘减法的分配。
*ˡ-sub : ∀ x y z → x * (y - z) ≡ x * y - x * z
*ˡ-sub = x[y-z]≈xy-xz +-*-ring

-- Subtracting a sum is iterated subtraction.
--
-- 嵌套减法：减去和即反复减法。
sub-+-assoc : ∀ X Y Z → X - (Y + Z) ≡ (X - Y) - Z
sub-+-assoc X Y Z = begin
  X - (Y + Z)
  ≡⟨ cong (X +_) (neg-distrib-+ Y Z) ⟩
  X + (- Y + - Z)
  ≡⟨ sym (+-assoc X (- Y) (- Z)) ⟩
  (X - Y) - Z ∎

------------------------------------------------------------------------
-- Four-term regrouping
--
-- 四项归组

-- Interleave-regroup two groups of four terms.
--
-- 两组四项交错归组。
pairs4 : ∀ x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ →
         (((x₁ + y₁) + (x₂ + y₂)) + ((x₃ + y₃) + (x₄ + y₄)))
         ≡ ((((x₁ + x₂) + x₃) + x₄) + (((y₁ + y₂) + y₃) + y₄))
pairs4 x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ = begin
    (((x₁ + y₁) + (x₂ + y₂)) + ((x₃ + y₃) + (x₄ + y₄)))
  ≡⟨ cong₂ _+_ (+interchange x₁ y₁ x₂ y₂)
               (+interchange x₃ y₃ x₄ y₄) ⟩
    (((x₁ + x₂) + (y₁ + y₂)) + ((x₃ + x₄) + (y₃ + y₄)))
  ≡⟨ +interchange (x₁ + x₂) (y₁ + y₂) (x₃ + x₄) (y₃ + y₄) ⟩
    (((x₁ + x₂) + (x₃ + x₄)) + ((y₁ + y₂) + (y₃ + y₄)))
  ≡⟨ cong₂ _+_ (sym (+-assoc (x₁ + x₂) x₃ x₄))
               (sym (+-assoc (y₁ + y₂) y₃ y₄)) ⟩
    ((((x₁ + x₂) + x₃) + x₄) + (((y₁ + y₂) + y₃) + y₄)) ∎

-- Rotate the first two summands to the end.
--
-- 前两个加项旋到末尾。
rot4 : ∀ X Y U V → ((X + Y) + U) + V ≡ ((U + V) + X) + Y
rot4 X Y U V = begin
  ((X + Y) + U) + V
  ≡⟨ +-assoc (X + Y) U V ⟩
  (X + Y) + (U + V)
  ≡⟨ +-comm (X + Y) (U + V) ⟩
  (U + V) + (X + Y)
  ≡⟨ sym (+-assoc (U + V) X Y) ⟩
  ((U + V) + X) + Y ∎

-- Reverse all four summands.
--
-- 四个加项整体反转。
rev4 : ∀ X Y U V → ((X + Y) + U) + V ≡ ((V + U) + Y) + X
rev4 X Y U V = begin
  ((X + Y) + U) + V
  ≡⟨ +-assoc (X + Y) U V ⟩
  (X + Y) + (U + V)
  ≡⟨ +-comm (X + Y) (U + V) ⟩
  (U + V) + (X + Y)
  ≡⟨ cong₂ _+_ (+-comm U V) (+-comm X Y) ⟩
  (V + U) + (Y + X)
  ≡⟨ sym (+-assoc (V + U) Y X) ⟩
  ((V + U) + Y) + X ∎

-- Negating a signed four-term sum flips all signs.
--
-- 对带符号的四项和整体取负会将所有符号翻转。
neg4 : ∀ a b c d →
       - (((a + b) + - c) + - d) ≡ ((- a + - b) + c) + d
neg4 a b c d = begin
    - (((a + b) + - c) + - d)
  ≡⟨ neg-distrib-+ ((a + b) + - c) (- d) ⟩
    - ((a + b) + - c) + - (- d)
  ≡⟨ cong₂ _+_ (inner a b c) (neg-involutive d) ⟩
    ((- a + - b) + c) + d ∎
  where
  inner : ∀ a b c → - ((a + b) + - c) ≡ (- a + - b) + c
  inner a b c = begin
    - ((a + b) + - c)
    ≡⟨ neg-distrib-+ (a + b) (- c) ⟩
    - (a + b) + - (- c)
    ≡⟨ cong (λ t → - (a + b) + t) (neg-involutive c) ⟩
    - (a + b) + c
    ≡⟨ cong (λ t → t + c) (neg-distrib-+ a b) ⟩
    (- a + - b) + c ∎

-- Negate the expansion of a two-term signed sum.
--
-- 对两项带符号和的展开取负。
foldNeg : ∀ x y → - (x + - y) ≡ - x + y
foldNeg x y = begin
  - (x + - y)
  ≡⟨ neg-distrib-+ x (- y) ⟩
  - x + - (- y)
  ≡⟨ cong (- x +_) (neg-involutive y) ⟩
  - x + y ∎

------------------------------------------------------------------------
-- Scalar rearrangement
--
-- 数乘重排

-- Scalar factors can be reordered.
--
-- 数乘因子之间可交换顺序。
swap-scalar : ∀ {r} s x → (s * (r * x)) ≡ r * (s * x)
swap-scalar {r} s x = begin
  s * (r * x)
  ≡⟨ sym (*-assoc s r x) ⟩
  (s * r) * x
  ≡⟨ cong (λ z → z * x) (*-comm s r) ⟩
  (r * s) * x
  ≡⟨ *-assoc r s x ⟩
  r * (s * x) ∎

-- Exchange the outer and inner scalar factors inside a product.
--
-- 在乘积内交换外层与内层数乘因子。
frontS : ∀ {r} s z x → (s * (r * x)) * z ≡ r * ((s * x) * z)
frontS {r} s z x = begin
  (s * (r * x)) * z
  ≡⟨ cong (λ t → t * z) (swap-scalar {r} s x) ⟩
  (r * (s * x)) * z
  ≡⟨ *-assoc r (s * x) z ⟩
  r * ((s * x) * z) ∎

-- Negation through a product of two scalar factors and an extra factor.
--
-- 对由两个数乘因子与一个额外因子构成的乘积取负。
front-negS : ∀ {r} s z x →
             - ((s * (r * x)) * z) ≡ r * (- ((s * x) * z))
front-negS {r} s z x = begin
  - ((s * (r * x)) * z)
  ≡⟨ cong -_ (frontS {r} s z x) ⟩
  - (r * ((s * x) * z))
  ≡⟨ neg-distribʳ-* r ((s * x) * z) ⟩
  r * (- ((s * x) * z)) ∎

-- Factor r out of a four-term signed sum.
--
-- 从四项带符号和里提出 r。
factor4 : ∀ {r} x y z w →
          (((r * x + r * y) + r * (- z)) + r * (- w))
          ≡ r * (((x + y) + - z) + - w)
factor4 {r} x y z w = begin
    (((r * x + r * y) + r * (- z)) + r * (- w))
  ≡⟨ cong (λ t → (t + r * (- z)) + r * (- w))
          (sym (*-distribˡ-+ r x y)) ⟩
    ((r * (x + y) + r * (- z)) + r * (- w))
  ≡⟨ cong (λ t → t + r * (- w))
          (sym (*-distribˡ-+ r (x + y) (- z))) ⟩
    r * ((x + y) + - z) + r * (- w)
  ≡⟨ sym (*-distribˡ-+ r ((x + y) + - z) (- w)) ⟩
    r * (((x + y) + - z) + - w) ∎

------------------------------------------------------------------------
-- Unit / zero normalisation
--
-- 单位/零规范化

-- Multiplying by one and subtracting zero leaves the value unchanged.
--
-- 乘以一后减去零乘积仍为原值。
norm1 : ∀ k → 1ℚ * k + - (0ℚ * k) ≡ k
norm1 k = begin
  1ℚ * k + - (0ℚ * k)
  ≡⟨ cong (λ x → 1ℚ * k + - x) (*-zeroˡ k) ⟩
  1ℚ * k + - 0ℚ
  ≡⟨ cong (λ x → x + - 0ℚ) (*-identityˡ k) ⟩
  k + - 0ℚ
  ≡⟨ +-identityʳ k ⟩
  k ∎

-- Three layers of zero leave the value unchanged.
--
-- 三层零相加仍为原值。
norm-tail : ∀ k → 0ℚ + (0ℚ + (0ℚ + k)) ≡ k
norm-tail k = begin
  0ℚ + (0ℚ + (0ℚ + k))
  ≡⟨ +-identityˡ (0ℚ + (0ℚ + k)) ⟩
  0ℚ + (0ℚ + k)
  ≡⟨ +-identityˡ (0ℚ + k) ⟩
  0ℚ + k
  ≡⟨ +-identityˡ k ⟩
  k ∎

------------------------------------------------------------------------
-- Rational bookkeeping for sums, differences and shifts
--
-- 求和、差与移位的记账引理

-- Adding a term and subtracting it again.
--
-- 先加后减同一项。
cancel-add : (x y : ℚ) → (x + y) + -_ y ≡ x
cancel-add x y =
  trans (+-assoc x y (-_ y))
    (trans (cong (x +_) (+-inverseʳ y)) (+-identityʳ x))

------------------------------------------------------------------------
-- Right cancellation for strict inequality
--
-- 严格不等式的右消去

-- (a + x) - (a + y) = x - y.
--
-- 同项相消的差值等式。
sub-cancel-common : (a x y : ℚ) → (a + x) - (a + y) ≡ x - y
sub-cancel-common a x y =
  begin
    (a + x) - (a + y)
      ≡⟨ cong (λ z → (a + x) + z) (neg-distrib-+ a y) ⟩
    (a + x) + (-_ a + -_ y)
      ≡⟨ sym (+-assoc (a + x) (-_ a) (-_ y)) ⟩
    ((a + x) + -_ a) + -_ y
      ≡⟨ cong (λ z → z + -_ y) red ⟩
    x + -_ y
  ∎
  where
    red : (a + x) + -_ a ≡ x
    red =
      begin
        (a + x) + -_ a
          ≡⟨ +-assoc a x (-_ a) ⟩
        a + (x + -_ a)
          ≡⟨ cong (λ z → a + z) (+-comm x (-_ a)) ⟩
        a + (-_ a + x)
          ≡⟨ sym (+-assoc a (-_ a) x) ⟩
        (a + -_ a) + x
          ≡⟨ cong (λ z → z + x) (+-inverseʳ a) ⟩
        0ℚ + x
          ≡⟨ +-identityˡ x ⟩
        x
      ∎

------------------------------------------------------------------------
-- (a + c) - (b + d) = (a - b) + (c - d)
--
-- 两项差之和的分配等式

-- A difference of sums splits into a sum of differences.
--
-- 两项和之差可以拆成两项差之和。
sub-add-split : (a b c d : ℚ) → (a + c) - (b + d) ≡ (a - b) + (c - d)
sub-add-split a b c d =
  begin
    (a + c) - (b + d)
      ≡⟨ cong (λ z → (a + c) + z) (neg-distrib-+ b d) ⟩
    (a + c) + (-_ b + -_ d)
      ≡⟨ sym (+-assoc (a + c) (-_ b) (-_ d)) ⟩
    ((a + c) + -_ b) + -_ d
      ≡⟨ cong (λ z → z + -_ d) mid ⟩
    ((a - b) + c) + -_ d
      ≡⟨ +-assoc (a - b) c (-_ d) ⟩
    (a - b) + (c + -_ d)
  ∎
  where
    mid : (a + c) + -_ b ≡ (a - b) + c
    mid =
      begin
        (a + c) + -_ b
          ≡⟨ cong (λ z → z + -_ b) (+-comm a c) ⟩
        (c + a) + -_ b
          ≡⟨ +-assoc c a (-_ b) ⟩
        c + (a + -_ b)
          ≡⟨ +-comm c (a + -_ b) ⟩
        (a - b) + c
      ∎

------------------------------------------------------------------------
-- (x - e) + e = x
--
-- 先减后加同一项

sub-shift-cancel : (x e : ℚ) → (x - e) + e ≡ x
sub-shift-cancel x e =
  begin
    (x - e) + e
      ≡⟨ +-assoc x (-_ e) e ⟩
    x + (-_ e + e)
      ≡⟨ cong (λ z → x + z) (+-comm (-_ e) e) ⟩
    x + (e + -_ e)
      ≡⟨ cong (λ z → x + z) (+-inverseʳ e) ⟩
    x + 0ℚ
      ≡⟨ +-identityʳ x ⟩
    x
  ∎

------------------------------------------------------------------------
-- The first-order term is the argument itself
--
-- 一阶项就是自变量本身

-- Moving a term across a strict bound.
--
-- 把加项搬过严格界。
lt-sub : (x y e : ℚ) → x < y + e → x - e < y
lt-sub x y e h =
  subst (λ z → x + -_ e < z) (cancel-add y e) (+-monoˡ-< (-_ e) h)

lt-add : (x y e : ℚ) → x - e < y → x < y + e
lt-add x y e h =
  subst (λ z → z < y + e) (sub-shift-cancel x e) (+-monoˡ-< e h)

lt-shift : (x y e : ℚ) → x + e < y → x < y - e
lt-shift x y e h =
  subst (λ z → z < y + -_ e) (cancel-add x e) (+-monoˡ-< (-_ e) h)

-- (b + c) + -_ b = c.
--
-- 消去首项的加法等式。
sub-sum-swap : (b c : ℚ) → (b + c) + -_ b ≡ c
sub-sum-swap b c =
  begin
    (b + c) + -_ b
      ≡⟨ cong (λ z → z + -_ b) (+-comm b c) ⟩
    (c + b) + -_ b
      ≡⟨ +-assoc c b (-_ b) ⟩
    c + (b + -_ b)
      ≡⟨ cong (c +_) (+-inverseʳ b) ⟩
    c + 0ℚ
      ≡⟨ +-identityʳ c ⟩
    c
  ∎

-- b + c <= a implies c <= a - b.
--
-- 非严格界的搬移。
le-sub-shift : (a b c : ℚ) → b + c ≤ a → c ≤ a - b
le-sub-shift a b c h =
  subst (λ z → z ≤ a + -_ b) (sub-sum-swap b c) (+-monoˡ-≤ (-_ b) h)

-- Two strict bounds subtract in opposite directions.
--
-- 两个严格界反向相减。
sub-lt : (a b c d : ℚ) → a < b → c < d → a - d < b - c
sub-lt a b c d h k =
  let s1 : a + -_ d < b + -_ d
      s1 = +-monoˡ-< (-_ d) h
      nd< : -_ d < -_ c
      nd< = neg-antimono-< k
      s2 : b + -_ d < b + -_ c
      s2 = +-monoʳ-< b nd<
  in <-trans s1 s2

-- Distribution of two subtractions.
--
-- 两层减法的分配等式。
sub-sub : (a b c d : ℚ) → (a - c) - (b + d) ≡ (a - b) - (c + d)
sub-sub a b c d =
  trans (cong (λ z → (a - c) + z) (neg-distrib-+ b d))
    (trans (+interchange a (-_ c) (-_ b) (-_ d))
           (cong (λ z → (a - b) + z) (sym (neg-distrib-+ c d))))

-- Strict monotonicity of expq.
-- j = suc (suc m) is the level at which four dyadic half-widths fit into
-- one dyadic width at level m, and m is chosen by delta-below so that
-- delta m < p - q. That is the only place where the two arguments' sizes
-- are used; everything else is the level-j bookkeeping of L3.
--
-- expq 的严格单调性。
-- 取 j = suc (suc m)：在第 j 层四个 delta j 恰好等于第 m 层的一个 delta，
-- 而 m 由 delta-below 选出使 delta m < p - q。两个自变量的大小只在这里
-- 用到；其余都是 L3 的第 j 层记账。
rotate-sum : (a x y z : ℚ) → ((a + x) + y) + z ≡ (a + z) + (x + y)
rotate-sum a x y z =
  let axz : (a + x) + z ≡ (a + z) + x
      axz = trans (+-assoc a x z)
              (trans (cong (a +_) (+-comm x z)) (sym (+-assoc a z x)))
      s1 : ((a + x) + y) + z ≡ (a + x) + (y + z)
      s1 = +-assoc (a + x) y z
      s2 : (a + x) + (y + z) ≡ (a + x) + (z + y)
      s2 = cong ((a + x) +_) (+-comm y z)
      s3 : (a + x) + (z + y) ≡ ((a + x) + z) + y
      s3 = sym (+-assoc (a + x) z y)
      s4 : ((a + x) + z) + y ≡ ((a + z) + x) + y
      s4 = cong (_+ y) axz
      s5 : ((a + z) + x) + y ≡ (a + z) + (x + y)
      s5 = +-assoc (a + z) x y
  in trans s1 (trans s2 (trans s3 (trans s4 s5)))

------------------------------------------------------------------------
-- Reversing a difference
--
-- 反转差式

-- neg (p - q) ≡ q - p: flipping the sign of a difference swaps its
-- operands.
--
-- neg (p - q) ≡ q - p：差式取反即交换两个操作数。
neg-sub : (p q : ℚ) → -_ (p - q) ≡ q - p
neg-sub p q =
  trans (neg-distrib-+ p (-_ q))
    (trans (cong (-_ p +_) (neg-involutive q)) (+-comm (-_ p) q))
