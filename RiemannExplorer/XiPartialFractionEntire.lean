/-
# ξ'/ξ 部分分式展开：任意零点处的级数留数（Hadamard 切片五）

本文件把 `XiPartialFractionResidue.lean` 中「上半平面非平凡零点」处的留数
结果推广到 ξ 的**任意零点**（含下半平面，经施瓦茨对称 `ξ(conj s) = conj(ξ s)`
共轭得到），并给出**单零点**处对数导数与配对 Mittag-Leffler 级数之差的
留数消失定理：

  `Tendsto (fun s => (s - s₀) * (ξ'/ξ s - c - F s)) (𝓝[≠] s₀) (𝓝 0)`

这是「ξ'/ξ − B − F 可延拓为整函数」论证的**级数侧可去奇点**输入：差函数
在零点去心邻域上可微（切片三、四），乘以 `(s − s₀)` 后极限为 0（本切片），
故奇点可去（下一切片用 `differentiableOn_update_limUnder_of_isLittleO`
粘合）。

## 证明纪律

无 `sorry`/`admit`/新公理；公理审计见 `Test/XiFunctionAxiomAudit.lean`。
-/

import RiemannExplorer.XiPartialFractionResidue

open Complex ComplexConjugate
open scoped BigOperators Topology

namespace RiemannExplorer

/-- 配对 Mittag-Leffler 项关于 `s ↦ conj s` 的共轭对称性。 -/
theorem xiPairedMittagLefflerTerm_conj (s ρ : ℂ) :
    xiPairedMittagLefflerTerm (conj s) ρ = conj (xiPairedMittagLefflerTerm s ρ) := by
  unfold xiPairedMittagLefflerTerm
  simp only [map_add, map_div₀, map_one, map_sub, Complex.conj_conj]
  ring

/-- 配对 Mittag-Leffler 级数和函数的共轭对称性：`F(conj s) = conj (F s)`。 -/
theorem xiPairedMittagLefflerSum_conj (s : ℂ) :
    xiPairedMittagLefflerSum (conj s) = conj (xiPairedMittagLefflerSum s) := by
  unfold xiPairedMittagLefflerSum
  rw [Complex.conj_tsum]
  exact tsum_congr fun ρ => xiPairedMittagLefflerTerm_conj s (ρ : ℂ)

/-- 级数在上半平面零点的共轭点处留数亦为 1（经共轭映射复合）。 -/
theorem tendsto_sub_mul_xiPairedMittagLefflerSum_conj
    (ρ₀ : UpperHalfPlaneNontrivialZero) :
    Filter.Tendsto (fun s => (s - conj (ρ₀ : ℂ)) * xiPairedMittagLefflerSum s)
      (𝓝[≠] (conj (ρ₀ : ℂ))) (𝓝 1) := by
  have hmap : Filter.Tendsto (conj : ℂ → ℂ) (𝓝[≠] (conj (ρ₀ : ℂ)))
      (𝓝[≠] (ρ₀ : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    have hc : Filter.Tendsto (conj : ℂ → ℂ) (𝓝 (conj (ρ₀ : ℂ))) (𝓝 (ρ₀ : ℂ)) := by
      have h := Complex.continuous_conj.tendsto (conj (ρ₀ : ℂ))
      rwa [Complex.conj_conj] at h
    have hne : ∀ᶠ s in 𝓝[≠] (conj (ρ₀ : ℂ)), conj s ≠ (ρ₀ : ℂ) := by
      rw [eventually_nhdsWithin_iff]
      exact Filter.Eventually.of_forall fun s hs heq =>
        hs (by have h := congrArg conj heq; rwa [Complex.conj_conj] at h)
    exact ⟨hc.mono_left nhdsWithin_le_nhds, hne⟩
  have h1 := (tendsto_sub_mul_xiPairedMittagLefflerSum ρ₀).comp hmap
  have h2 := (Complex.continuous_conj.tendsto (1 : ℂ)).comp h1
  rw [map_one] at h2
  refine h2.congr' (Filter.Eventually.of_forall fun s => ?_)
  show conj ((conj s - (ρ₀ : ℂ)) * xiPairedMittagLefflerSum (conj s)) =
    (s - conj (ρ₀ : ℂ)) * xiPairedMittagLefflerSum s
  rw [map_mul, map_sub, Complex.conj_conj, xiPairedMittagLefflerSum_conj,
    Complex.conj_conj]

/-- 级数在 ζ 的**任意**非平凡零点（虚部非零）处留数为 1。 -/
theorem tendsto_sub_mul_xiPairedMittagLefflerSum_of_zero {s₀ : ℂ}
    (hz : RiemannHypothesis.IsNontrivialZero s₀) (him : s₀.im ≠ 0) :
    Filter.Tendsto (fun s => (s - s₀) * xiPairedMittagLefflerSum s)
      (𝓝[≠] s₀) (𝓝 1) := by
  rcases lt_or_gt_of_ne him with hlt | hgt
  · -- s₀.im < 0：conj s₀ 是上半平面非平凡零点
    have h0' : 0 < (conj s₀).re := by rw [Complex.conj_re]; exact hz.2.1
    have h1' : (conj s₀).re < 1 := by rw [Complex.conj_re]; exact hz.2.2
    have hξs₀ : xiFunction s₀ = 0 :=
      (xiFunction_eq_zero_iff hz.2.1 hz.2.2).mpr hz.1
    have hξc : xiFunction (conj s₀) = 0 := by
      rw [xiFunction_conj, hξs₀, map_zero]
    have hζc : riemannZeta (conj s₀) = 0 := (xiFunction_eq_zero_iff h0' h1').mp hξc
    have himc : 0 < (conj s₀).im := by rw [Complex.conj_im]; linarith
    have h3 := tendsto_sub_mul_xiPairedMittagLefflerSum_conj
      ⟨conj s₀, ⟨⟨hζc, h0', h1'⟩, himc⟩⟩
    have h3' : Filter.Tendsto
        (fun s => (s - conj (conj s₀)) * xiPairedMittagLefflerSum s)
        (𝓝[≠] (conj (conj s₀))) (𝓝 1) := h3
    rwa [Complex.conj_conj] at h3'
  · exact tendsto_sub_mul_xiPairedMittagLefflerSum ⟨s₀, hz, hgt⟩

/-- 任意非平凡零点处，`(s − s₀)·(ξ'/ξ − F)` 的极限为「解析重数 − 1」。 -/
theorem tendsto_sub_mul_logDeriv_sub_xiPairedMittagLefflerSum_of_zero {s₀ : ℂ}
    (hz : RiemannHypothesis.IsNontrivialZero s₀) (him : s₀.im ≠ 0) :
    Filter.Tendsto
      (fun s => (s - s₀) * (deriv xiFunction s / xiFunction s -
        xiPairedMittagLefflerSum s))
      (𝓝[≠] s₀) (𝓝 ((analyticOrderNatAt xiFunction s₀ : ℂ) - 1)) := by
  have h1 := tendsto_sub_mul_logDeriv_xiFunction_of_zero
    ((xiFunction_eq_zero_iff hz.2.1 hz.2.2).mpr hz.1)
  have h2 := tendsto_sub_mul_xiPairedMittagLefflerSum_of_zero hz him
  have h3 := h1.sub h2
  refine h3.congr' (Filter.Eventually.of_forall fun s => ?_)
  show (s - s₀) * (deriv xiFunction s / xiFunction s) -
      (s - s₀) * xiPairedMittagLefflerSum s =
    (s - s₀) * (deriv xiFunction s / xiFunction s - xiPairedMittagLefflerSum s)
  rw [mul_sub]

/-- **单零点**处差函数的留数消失：`(s − s₀)·(ξ'/ξ − c − F) → 0`。
这是差函数在 `s₀` 处奇点可去的 `isLittleO` 输入。 -/
theorem tendsto_sub_mul_logDeriv_sub_const_sub_xiPairedMittagLefflerSum_of_zero
    (c : ℂ) {s₀ : ℂ}
    (hz : RiemannHypothesis.IsNontrivialZero s₀) (him : s₀.im ≠ 0)
    (hs : analyticOrderNatAt xiFunction s₀ = 1) :
    Filter.Tendsto
      (fun s => (s - s₀) * (deriv xiFunction s / xiFunction s - c -
        xiPairedMittagLefflerSum s))
      (𝓝[≠] s₀) (𝓝 0) := by
  have h1 := tendsto_sub_mul_logDeriv_sub_xiPairedMittagLefflerSum_of_zero hz him
  rw [hs] at h1
  simp only [Nat.cast_one, sub_self] at h1
  have hsub0 : Filter.Tendsto (fun s : ℂ => s - s₀) (𝓝[≠] s₀) (𝓝 0) := by
    have h : Filter.Tendsto (fun s : ℂ => s - s₀) (𝓝 s₀) (𝓝 0) := by
      have h := (continuous_sub_right s₀).tendsto s₀
      simpa using h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun s => (s - s₀) * c) (𝓝[≠] s₀) (𝓝 0) := by
    have hc0 : Filter.Tendsto (fun _ : ℂ => c) (𝓝[≠] s₀) (𝓝 c) := tendsto_const_nhds
    have h := hsub0.mul hc0
    rwa [zero_mul] at h
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  refine h3.congr' (Filter.Eventually.of_forall fun s => ?_)
  ring

end RiemannExplorer
