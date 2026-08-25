import HardyTheorem.SelbergJDiagonalTermBridge

namespace HardyTheorem

/-! # Equivalence between positive diagonal pairs and one gcd-ray scale -/

def selbergDiagonalRayIndex (A B : ℕ) :=
  {p : ℕ × ℕ // (p.1 + 1) * A = (p.2 + 1) * B}

noncomputable def selbergDiagonalRayScale
    {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (p : selbergDiagonalRayIndex A B) : ℕ :=
  Classical.choose ((selberg_diagonal_equation_iff_unique_gcd_ray
    hA hB (Nat.le_add_left 1 p.1.1) (Nat.le_add_left 1 p.1.2)).mp p.property)

theorem selbergDiagonalRayScale_spec
    {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (p : selbergDiagonalRayIndex A B) :
    1 ≤ selbergDiagonalRayScale hA hB p ∧
      p.1.1 + 1 = selbergDiagonalRayScale hA hB p * (B / Nat.gcd A B) ∧
      p.1.2 + 1 = selbergDiagonalRayScale hA hB p * (A / Nat.gcd A B) :=
  Classical.choose_spec ((selberg_diagonal_equation_iff_unique_gcd_ray
    hA hB (Nat.le_add_left 1 p.1.1) (Nat.le_add_left 1 p.1.2)).mp p.property) |>.1

noncomputable def selbergDiagonalRayEquiv
    {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    selbergDiagonalRayIndex A B ≃ ℕ where
  toFun p := selbergDiagonalRayScale hA hB p - 1
  invFun j := by
    let g := Nat.gcd A B
    let A' := A / g
    let B' := B / g
    have hg : 0 < g := Nat.gcd_pos_of_pos_left B (zero_lt_one.trans_le hA)
    have hA' : 0 < A' := Nat.div_pos
      (Nat.le_of_dvd (zero_lt_one.trans_le hA) (Nat.gcd_dvd_left A B)) hg
    have hB' : 0 < B' := Nat.div_pos
      (Nat.le_of_dvd (zero_lt_one.trans_le hB) (Nat.gcd_dvd_right A B)) hg
    refine ⟨((j + 1) * B' - 1, (j + 1) * A' - 1), ?_⟩
    have hmpos : 0 < (j + 1) * B' := Nat.mul_pos (by omega) hB'
    have hnpos : 0 < (j + 1) * A' := Nat.mul_pos (by omega) hA'
    have hm : ((j + 1) * B' - 1) + 1 = (j + 1) * B' := by omega
    have hn : ((j + 1) * A' - 1) + 1 = (j + 1) * A' := by omega
    have hgA : g * A' = A := Nat.mul_div_cancel' (Nat.gcd_dvd_left A B)
    have hgB : g * B' = B := Nat.mul_div_cancel' (Nat.gcd_dvd_right A B)
    rw [hm, hn, ← hgA, ← hgB]
    ring
  left_inv p := by
    let g := Nat.gcd A B
    let A' := A / g
    let B' := B / g
    have hg : 0 < g := Nat.gcd_pos_of_pos_left B (zero_lt_one.trans_le hA)
    have hA' : 0 < A' := Nat.div_pos
      (Nat.le_of_dvd (zero_lt_one.trans_le hA) (Nat.gcd_dvd_left A B)) hg
    have hB' : 0 < B' := Nat.div_pos
      (Nat.le_of_dvd (zero_lt_one.trans_le hB) (Nat.gcd_dvd_right A B)) hg
    have hs := selbergDiagonalRayScale_spec hA hB p
    apply Subtype.ext
    apply Prod.ext
    · change ((selbergDiagonalRayScale hA hB p - 1 + 1) * B' - 1) = p.1.1
      rw [show selbergDiagonalRayScale hA hB p - 1 + 1 =
        selbergDiagonalRayScale hA hB p by omega]
      rw [← hs.2.1]
      omega
    · change ((selbergDiagonalRayScale hA hB p - 1 + 1) * A' - 1) = p.1.2
      rw [show selbergDiagonalRayScale hA hB p - 1 + 1 =
        selbergDiagonalRayScale hA hB p by omega]
      rw [← hs.2.2]
      omega
  right_inv j := by
    let g := Nat.gcd A B
    let A' := A / g
    let B' := B / g
    have hg : 0 < g := Nat.gcd_pos_of_pos_left B (zero_lt_one.trans_le hA)
    have hB' : 0 < B' := Nat.div_pos
      (Nat.le_of_dvd (zero_lt_one.trans_le hB) (Nat.gcd_dvd_right A B)) hg
    let p : selbergDiagonalRayIndex A B := by
      have hA' : 0 < A' := Nat.div_pos
        (Nat.le_of_dvd (zero_lt_one.trans_le hA) (Nat.gcd_dvd_left A B)) hg
      refine ⟨((j + 1) * B' - 1, (j + 1) * A' - 1), ?_⟩
      have hmpos : 0 < (j + 1) * B' := Nat.mul_pos (by omega) hB'
      have hnpos : 0 < (j + 1) * A' := Nat.mul_pos (by omega) hA'
      have hm : ((j + 1) * B' - 1) + 1 = (j + 1) * B' := by omega
      have hn : ((j + 1) * A' - 1) + 1 = (j + 1) * A' := by omega
      have hgA : g * A' = A := Nat.mul_div_cancel' (Nat.gcd_dvd_left A B)
      have hgB : g * B' = B := Nat.mul_div_cancel' (Nat.gcd_dvd_right A B)
      rw [hm, hn, ← hgA, ← hgB]
      ring
    have hs := selbergDiagonalRayScale_spec hA hB p
    have hpfirst : p.1.1 + 1 = (j + 1) * B' := by
      have hmpos : 0 < (j + 1) * B' := Nat.mul_pos (by omega) hB'
      dsimp [p]
      omega
    have hscale : selbergDiagonalRayScale hA hB p = j + 1 := by
      apply Nat.eq_of_mul_eq_mul_right hB'
      rw [← hs.2.1, hpfirst]
    change selbergDiagonalRayScale hA hB p - 1 = j
    rw [hscale]
    omega

end HardyTheorem
