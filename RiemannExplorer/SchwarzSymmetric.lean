/-
# Schwarz 对称函数的导数（一般复分析引理）

本文件提供 Li 系数实值性证明所需的一般复分析工具：

- `deriv_schwarzSymmetricOn`：在开集 `U`（共轭稳定）上可微且满足
  Schwarz 对称 `G (conj z) = conj (G z)` 的函数，其导数仍满足 Schwarz 对称。
  证明用 `HasDerivAt.conj_conj`（Mathlib 的 `Deriv/Star` 工具）加上
  局部相等函数导数相同。
- `schwarzSymmetric_iteratedDeriv`：归纳得到任意阶迭代导数仍 Schwarz 对称。
- `iteratedDeriv_schwarz_real`：在实点 `a ∈ U` 处，任意阶迭代导数取实值。

这些是纯复分析引理，与 ζ/ξ 无关；应用见
`RiemannExplorer/LiReality.lean`（λ_n 的实值性）。
-/

import RiemannExplorer

open Complex ComplexConjugate Topology

namespace RiemannExplorer

/-- Schwarz 对称在求导下保持：设 `U` 开且共轭稳定，`G` 在 `U` 上可微并满足
`G (conj z) = conj (G z)`，则对 `z ∈ U` 有
`deriv G (conj z) = conj (deriv G z)`。 -/
theorem deriv_schwarzSymmetricOn {G : ℂ → ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hUconj : ∀ z ∈ U, conj z ∈ U)
    (hdiff : DifferentiableOn ℂ G U)
    (hsym : ∀ z ∈ U, G (conj z) = conj (G z))
    {z : ℂ} (hz : z ∈ U) :
    deriv G (conj z) = conj (deriv G z) := by
  have hcz : conj z ∈ U := hUconj z hz
  have hG : HasDerivAt G (deriv G z) z :=
    ((hdiff z hz).differentiableAt (hUopen.mem_nhds hz)).hasDerivAt
  set g : ℂ → ℂ := fun w ↦ conj (G (conj w)) with hg
  have hg_eq : g =ᶠ[𝓝 (conj z)] G := by
    filter_upwards [hUopen.mem_nhds hcz] with w hw
    show conj (G (conj w)) = G w
    rw [hsym w hw]
    exact Complex.conj_conj _
  have hgderiv : HasDerivAt g (conj (deriv G z)) (conj z) := hG.conj_conj
  exact ((Filter.EventuallyEq.hasDerivAt_iff hg_eq).mp hgderiv).deriv

/-- `DifferentiableOn` 的函数在开集上的导数仍可微
（Mathlib `DifferentiableOn.deriv` 的本地别名，便于引用）。 -/
theorem differentiableOn_deriv {G : ℂ → ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hdiff : DifferentiableOn ℂ G U) :
    DifferentiableOn ℂ (deriv G) U :=
  hdiff.deriv hUopen

/-- 归纳主引理：在开、共轭稳定集 `U` 上可微且 Schwarz 对称的 `F`，
其任意阶迭代导数在 `U` 上仍可微且仍 Schwarz 对称。 -/
theorem schwarzSymmetric_iteratedDeriv {F : ℂ → ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hUconj : ∀ z ∈ U, conj z ∈ U)
    (hdiff : DifferentiableOn ℂ F U)
    (hsym : ∀ z ∈ U, F (conj z) = conj (F z)) (m : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv m F) U ∧
      ∀ z ∈ U, iteratedDeriv m F (conj z) = conj (iteratedDeriv m F z) := by
  induction m with
  | zero =>
    rw [iteratedDeriv_zero]
    exact ⟨hdiff, hsym⟩
  | succ m ih =>
    rw [iteratedDeriv_succ]
    exact ⟨differentiableOn_deriv hUopen ih.1,
      fun z hz ↦ deriv_schwarzSymmetricOn hUopen hUconj ih.1 ih.2 hz⟩

/-- 主定理：Schwarz 对称的可微函数在实点处的任意阶迭代导数为实数。 -/
theorem iteratedDeriv_schwarz_real {F : ℂ → ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hUconj : ∀ z ∈ U, conj z ∈ U)
    (hdiff : DifferentiableOn ℂ F U)
    (hsym : ∀ z ∈ U, F (conj z) = conj (F z))
    {a : ℝ} (ha : (a : ℂ) ∈ U) (m : ℕ) :
    ∃ r : ℝ, iteratedDeriv m F (a : ℂ) = (r : ℂ) := by
  have hsyma := (schwarzSymmetric_iteratedDeriv hUopen hUconj hdiff hsym m).2 _ ha
  rw [conj_ofReal] at hsyma
  exact ⟨(iteratedDeriv m F (a : ℂ)).re,
    (Complex.conj_eq_iff_re.mp hsyma.symm).symm⟩

end RiemannExplorer
