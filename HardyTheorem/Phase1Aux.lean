/-
# Hardy D 链 Phase 1 辅助引理

本文件集中 Phase 1 的 bornology-upgrade 路径与 generic asymptotic sign
引理。结构上分为三块:

1. `hardyZ_eventually_const_sign_of_bounded_zeros`:
   Bornology.IsBounded 版本的 hardyZ 事件常号。
   此 lemma 的完整证明在 `HardyTheorem.lean`(`HardyTheorem` 命名空间)。
   本文件在 `HardyTheorem.Phase1Aux` 命名空间下提供重新入口,
   便于下游模块统一通过 `HardyTheorem.Phase1Aux` 调用。

2. `weightedIntegralOf_eventually_positive_from_tail_target`:
   weightedIntegralOf + tail-dominance + 事件正 → 渐近正。
   (与 `HardyTheorem.weightedIntegralOf_eventually_positive_of_tail_dominates`
   等价,提供 Phase1Aux 命名空间下的别名便于下游统一调用。)

3. 两个 generic asymptotic sign 引理(基于 `~[l]`,asymptotic equivalent):
   - `eventually_positive_of_asympEquiv_of_eventually_positive`:
     `f ~[l] g` + `g > 0` 事件 → `f > 0` 事件
   - `asymptotic_sign_preserved_under_eventual_const`:
     `f ~[l] g` + `f > 0` 事件 → `g > 0` 事件
   这两个 lemma 与 `~[atTop]`(asymptotic equivalent)API 配合,
   表达"渐近相同的两个函数保持事件符号"。

## 注意(对 brief 的一处校正)
任务卡原始写法是 `eventually_positive_of_bigO_of_eventually_positive`,
但 `f = O[g]` + `g > 0` 不足以推出 `f > 0`(大 O 只给出 `|f| ≤ C*g`)。
正确的 generic 引理必须用 `~[l]`(asymptotic equivalent),
其语义是 `f/g → 1`,从而保证 `f` 与 `g` 在事件上同号。
-/

import HardyTheorem

open Asymptotics Filter Topology

namespace HardyTheorem.Phase1Aux

/-! ## 1. bornology-upgrade 入口: hardyZ 事件常号 (Bornology.IsBounded 版本) -/

/-- Bornology.IsBounded 版本的 hardyZ 事件常号。

完整证明见 `HardyTheorem.hardyZ_eventually_const_sign_of_bounded_zeros`
(在 `HardyTheorem.lean` 中),本引理作为 `HardyTheorem.Phase1Aux` 命名空间下
的统一入口。 -/
lemma hardyZ_eventually_const_sign_of_bounded_zeros
    (h_bdd : Bornology.IsBounded {t : ℝ | hardyZ t = 0}) :
    (∀ᶠ t in atTop, hardyZ t > 0) ∨ (∀ᶠ t in atTop, hardyZ t < 0) :=
  HardyTheorem.hardyZ_eventually_const_sign_of_bounded_zeros h_bdd

/-! ## 2. tail-dominance + 事件正 → weightedIntegralOf 渐近正 -/

/-- Phase1Aux 入口: weightedIntegralOf 在 tail-dominance + 事件正下渐近正。

本引理与 `HardyTheorem.weightedIntegralOf_eventually_positive_of_tail_dominates`
逻辑等价(同样的连续性 + 事件正 + tail-dominates 假设,同样的事件正结论);
名字 `_from_tail_target` 强调假设是
`HardyTheorem.weightedIntegralOf_tail_dominates` 这个 Prop-valued 谓词,
便于下游按 "tail-dominance target → 渐近正" 的方向调用。 -/
lemma weightedIntegralOf_eventually_positive_from_tail_target
    (f : ℝ → ℝ) (n : ℕ) (hf : Continuous f)
    (h_pos : ∀ᶠ t in atTop, f t > 0)
    (h_tail : HardyTheorem.weightedIntegralOf_tail_dominates f n) :
    ∀ᶠ T in atTop, HardyTheorem.weightedIntegralOf f n T > 0 :=
  HardyTheorem.weightedIntegralOf_eventually_positive_of_tail_dominates
    f n hf h_pos h_tail

/-! ## 3. generic asymptotic sign 引理 -/

/-- 通用引理:若 `f ~[l] g` 且 `g` 在 filter `l` 下最终为正,则 `f` 也最终为正。

证明思路:
1. `f ~[l] g` 加 `g ≠ 0` 事件版本 ⇒ `f/g → 1` (用 `isEquivalent_iff_tendsto_one`)
2. `1 > 0` ⇒ `f/g` 最终为正 (`Tendsto.eventually`)
3. 逐点重写 `f = (f/g) * g`,两端都是正,乘积为正。

注意:与 `f = O[l] g` 不同,asymptotic equivalent 给出 *正比* 关系,
足以把"正"从 `g` 传播到 `f`。 -/
lemma eventually_positive_of_asympEquiv_of_eventually_positive
    {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hfg : f ~[l] g) (hg : ∀ᶠ x in l, 0 < g x) :
    ∀ᶠ x in l, 0 < f x := by
  have hg_ne : ∀ᶠ x in l, g x ≠ 0 := hg.mono fun _ hx => ne_of_gt hx
  have hfg_one : Tendsto (fun x => f x / g x) l (𝓝 (1 : ℝ)) :=
    (isEquivalent_iff_tendsto_one hg_ne).mp hfg
  have hU : {y : ℝ | 0 < y} ∈ 𝓝 (1 : ℝ) := Ioi_mem_nhds one_pos
  have hfg_pos : ∀ᶠ x in l, 0 < f x / g x := hfg_one.eventually hU
  filter_upwards [hfg_pos, hg] with x hx_div hx_g
  have hg_ne_x : g x ≠ 0 := ne_of_gt hx_g
  have hkey : (f x / g x) * g x = f x := div_mul_cancel₀ (f x) hg_ne_x
  rw [← hkey]
  exact mul_pos hx_div hx_g

/-- 通用引理:若 `f ~[l] g` 且 `f` 在 filter `l` 下最终为正,则 `g` 也最终为正。

由 `~[l]` 的对称性,这是
`eventually_positive_of_asympEquiv_of_eventually_positive` 的直接推论:
将 `f,g` 对调即可。 -/
lemma asymptotic_sign_preserved_under_eventual_const
    {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hfg : f ~[l] g) (hf : ∀ᶠ x in l, 0 < f x) :
    ∀ᶠ x in l, 0 < g x :=
  eventually_positive_of_asympEquiv_of_eventually_positive hfg.symm hf

end HardyTheorem.Phase1Aux
