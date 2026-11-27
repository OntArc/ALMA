------------------------------------------------------------------------
-- Suprema reached from below
--
-- 自下方逼近的上确界
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.OrderComplete.Limit where

open import Data.Product using (Σ; _×_; _,_)
open import Data.Rational using (ℚ)

open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Base using
  (Subset; Located; _≤ℝ_)
open import Real.Interval.OrderComplete using (sup; sup-upper)

------------------------------------------------------------------------
-- A point below which the set is unbounded
--
-- 集合在其下方无界的点

-- A located set with a member and an upper bound has a supremum s. If
-- every x strictly below the rational point q has a member y above it,
-- then s cannot lie strictly below q: such a y would be a member, hence
-- y ≤ s, and s < y would put s strictly below itself. So q ≤ s. This is
-- the "sup is the limit of members" fact, taken in the shape needed to
-- read a rational point off the cut; it never unfolds the set itself
-- The set, the locatedness proof, the initial member and the upper bound
-- are passed as the same arguments that build the supremum, so at a call
-- site the term below is the very term that was built there.
--
-- 已定位、非空且有上界的集合有上确界 s。若每个严格低于有理点 q 的 x
-- 都有成员 y 压在其上，则 s 不可能严格低于 q：那个 y 是成员，故 y ≤ s，
-- 而 s < y 会把 s 严格置于自身之下。于是 q ≤ s。这就是"上确界是成员的
-- 极限"这一事实，取成从割上读出有理点所需的形状；它从不展开集合本身
-- 集合、定位性证明、初始成员与上界，与构造上确界时所用的是同一批参数，
-- 因此在调用处，下面的项就是那里构造出来的那个项。
sup-≤-of-limit : {P : Subset} (loc : Located P)
                 {x₀ : RealI} (px₀ : P x₀) {u₀ : RealI}
                 (isUpper : (x : RealI) → P x → x ≤ℝ u₀)
               → (q : ℚ)
               → ((x : RealI) → x <ℝ embedℚ q
                                  → Σ RealI (λ y → P y × (x <ℝ y)))
               → embedℚ q ≤ℝ sup {P = P} loc {x₀ = x₀} px₀ {u₀ = u₀} isUpper
sup-≤-of-limit loc px₀ isUpper q lim s<eq =
  let
    y , (py , s<y) =
      lim (sup {P = _} loc {x₀ = _} px₀ {u₀ = _} isUpper) s<eq
    y≤s = sup-upper {P = _} loc {x₀ = _} px₀ {u₀ = _} isUpper y py
  in
    y≤s s<y
