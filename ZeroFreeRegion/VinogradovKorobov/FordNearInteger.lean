import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Archimedean

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Integers `d` with `|d| ≤ K` for which `d * γ` lies within `δ` of its
nearest integer.  This is the finite set counted in Ford's equation (5.6). -/
noncomputable def fordNearIntegerSet
    (K : ℕ) (γ δ : ℝ) : Finset ℤ :=
  (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter fun d ↦
    |(d : ℝ) * γ - (round ((d : ℝ) * γ) : ℝ)| < δ

theorem mem_fordNearIntegerSet
    (K : ℕ) (γ δ : ℝ) (d : ℤ) :
    d ∈ fordNearIntegerSet K γ δ ↔
      -(K : ℤ) ≤ d ∧ d ≤ (K : ℤ) ∧
        |(d : ℝ) * γ - (round ((d : ℝ) * γ) : ℝ)| < δ := by
  simp [fordNearIntegerSet, and_assoc]

/-- A finite set of integers contained in a real open interval has cardinality
at most the interval length plus one. -/
private theorem int_finset_card_cast_le_sub_add_one
    (S : Finset ℤ) (a b : ℝ) (hab : a ≤ b)
    (hS : ∀ z ∈ S, a < (z : ℝ) ∧ (z : ℝ) < b) :
    (S.card : ℝ) ≤ b - a + 1 := by
  classical
  by_cases hEmpty : S = ∅
  · rw [hEmpty]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  have hsubset :
      S ⊆ Finset.Icc (⌊a⌋ + 1) (⌈b⌉ - 1) := by
    intro z hz
    rw [Finset.mem_Icc]
    constructor
    · exact (Int.add_one_le_iff.mpr (Int.floor_lt.mpr (hS z hz).1))
    · exact (Int.le_sub_one_iff.mpr (Int.lt_ceil.mpr (hS z hz).2))
  have hcard :
      S.card ≤ (⌈b⌉ - ⌊a⌋ - 1).toNat := by
    exact (Finset.card_le_card hsubset).trans_eq (by
      rw [Int.card_Icc]
      congr 1
      omega)
  have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨z, hz⟩ := hnonempty
  have hcountNonneg : 0 ≤ ⌈b⌉ - ⌊a⌋ - 1 := by
    have hfloor : ⌊a⌋ < z := Int.floor_lt.mpr (hS z hz).1
    have hceil : z < ⌈b⌉ := Int.lt_ceil.mpr (hS z hz).2
    omega
  have hcast :
      (((⌈b⌉ - ⌊a⌋ - 1).toNat : ℕ) : ℝ) =
        ((⌈b⌉ - ⌊a⌋ - 1 : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hcountNonneg
  have hfloorLower : (a : ℝ) - 1 < (⌊a⌋ : ℤ) := by
    exact_mod_cast Int.sub_one_lt_floor a
  have hceilUpper : ((⌈b⌉ : ℤ) : ℝ) < b + 1 := by
    exact_mod_cast Int.ceil_lt_add_one b
  calc
    (S.card : ℝ) ≤
        (((⌈b⌉ - ⌊a⌋ - 1).toNat : ℕ) : ℝ) := by
      exact_mod_cast hcard
    _ = ((⌈b⌉ - ⌊a⌋ - 1 : ℤ) : ℝ) := hcast
    _ ≤ b - a + 1 := by
      push_cast
      linarith

/-- Ford's elementary near-integer count, equation (5.6), in the form needed
for the later coefficient-window bounds. -/
theorem card_fordNearIntegerSet_le
    (K : ℕ) (γ δ : ℝ) (hγ : 0 < γ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) :
    ((fordNearIntegerSet K γ δ).card : ℝ) ≤
      4 * (K : ℝ) * δ + 2 * (K : ℝ) * γ + 4 * δ / γ + 2 := by
  classical
  let S := fordNearIntegerSet K γ δ
  let nearest : ℤ → ℤ := fun d ↦ round ((d : ℝ) * γ)
  let T := S.image nearest
  have hdecompose :
      (S.card : ℝ) =
        ∑ m ∈ T, ((S.filter fun d ↦ nearest d = m).card : ℝ) := by
    have hnat :=
      Finset.card_eq_sum_card_image nearest S
    change (S.card : ℝ) =
      ∑ m ∈ S.image nearest,
        ((S.filter fun d ↦ nearest d = m).card : ℝ)
    simp only [← Nat.cast_sum]
    exact_mod_cast hnat
  have hT :
      (T.card : ℝ) ≤ 2 * (K : ℝ) * γ + 2 := by
    have hinterval :
        (T.card : ℝ) ≤
          ((K : ℝ) * γ + δ) -
            (-((K : ℝ) * γ + δ)) + 1 := by
      apply int_finset_card_cast_le_sub_add_one
      · linarith [mul_nonneg (Nat.cast_nonneg K) hγ.le]
      · intro m hm
        obtain ⟨d, hdS, rfl⟩ := Finset.mem_image.mp hm
        have hd := (mem_fordNearIntegerSet K γ δ d).mp hdS
        have hdLower : -(K : ℝ) ≤ (d : ℝ) := by
          exact_mod_cast hd.1
        have hdUpper : (d : ℝ) ≤ (K : ℝ) := by
          exact_mod_cast hd.2.1
        have hxLower :
            -((K : ℝ) * γ) ≤ (d : ℝ) * γ := by
          nlinarith
        have hxUpper :
            (d : ℝ) * γ ≤ (K : ℝ) * γ := by
          nlinarith
        have hnear := abs_lt.mp hd.2.2
        constructor <;> linarith
    calc
      (T.card : ℝ) ≤
          ((K : ℝ) * γ + δ) -
            (-((K : ℝ) * γ + δ)) + 1 := hinterval
      _ ≤ 2 * (K : ℝ) * γ + 2 := by linarith
  have hfiber (m : ℤ) (hm : m ∈ T) :
      ((S.filter fun d ↦ nearest d = m).card : ℝ) ≤
        2 * δ / γ + 1 := by
    have hinterval :
        ((S.filter fun d ↦ nearest d = m).card : ℝ) ≤
          ((m : ℝ) + δ) / γ - ((m : ℝ) - δ) / γ + 1 := by
      apply int_finset_card_cast_le_sub_add_one
      · apply (div_le_div_iff_of_pos_right hγ).2
        linarith
      · intro d hd
        have hdFilter := Finset.mem_filter.mp hd
        have hdS :=
          (mem_fordNearIntegerSet K γ δ d).mp hdFilter.1
        have hround : round ((d : ℝ) * γ) = m := hdFilter.2
        have hnear := abs_lt.mp hdS.2.2
        rw [hround] at hnear
        constructor
        · rw [div_lt_iff₀ hγ]
          linarith
        · rw [lt_div_iff₀ hγ]
          linarith
    calc
      ((S.filter fun d ↦ nearest d = m).card : ℝ) ≤
          ((m : ℝ) + δ) / γ - ((m : ℝ) - δ) / γ + 1 :=
        hinterval
      _ = 2 * δ / γ + 1 := by ring
  have hfactor : 0 ≤ 2 * δ / γ + 1 := by positivity
  calc
    ((fordNearIntegerSet K γ δ).card : ℝ) = (S.card : ℝ) := rfl
    _ = ∑ m ∈ T, ((S.filter fun d ↦ nearest d = m).card : ℝ) :=
      hdecompose
    _ ≤ ∑ _m ∈ T, (2 * δ / γ + 1) := by
      apply Finset.sum_le_sum
      intro m hm
      exact hfiber m hm
    _ = (T.card : ℝ) * (2 * δ / γ + 1) := by simp
    _ ≤ (2 * (K : ℝ) * γ + 2) * (2 * δ / γ + 1) :=
      mul_le_mul_of_nonneg_right hT hfactor
    _ = 4 * (K : ℝ) * δ + 2 * (K : ℝ) * γ +
        4 * δ / γ + 2 := by
      field_simp [hγ.ne']
      ring

/-- Scaled form used in Ford's `W_j`: substituting `δ = 1/(2A)` and any
integer cutoff `K ≤ B` gives the four explicit terms that are later bounded
degree by degree. -/
theorem card_fordNearIntegerSet_le_scaled
    (K A B : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hA : 1 ≤ A) (hK : K ≤ B) :
    ((fordNearIntegerSet K γ (1 / (2 * (A : ℝ)))).card : ℝ) ≤
      2 * (B : ℝ) / (A : ℝ) + 2 * (B : ℝ) * γ +
        2 / ((A : ℝ) * γ) + 2 := by
  have hAreal : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hApos : (0 : ℝ) < (A : ℝ) := zero_lt_one.trans_le hAreal
  have hδ0 : 0 ≤ 1 / (2 * (A : ℝ)) := by positivity
  have hδ :
      1 / (2 * (A : ℝ)) ≤ (1 : ℝ) / 2 := by
    apply one_div_le_one_div_of_le
    · norm_num
    · nlinarith
  have hbase :=
    card_fordNearIntegerSet_le K γ (1 / (2 * (A : ℝ)))
      hγ hδ0 hδ
  have hKreal : (K : ℝ) ≤ (B : ℝ) := by exact_mod_cast hK
  have hfirst :
      4 * (K : ℝ) * (1 / (2 * (A : ℝ))) ≤
        4 * (B : ℝ) * (1 / (2 * (A : ℝ))) := by
    gcongr
  have hsecond :
      2 * (K : ℝ) * γ ≤ 2 * (B : ℝ) * γ := by
    gcongr
  calc
    ((fordNearIntegerSet K γ (1 / (2 * (A : ℝ)))).card : ℝ) ≤
        4 * (K : ℝ) * (1 / (2 * (A : ℝ))) +
          2 * (K : ℝ) * γ +
          4 * (1 / (2 * (A : ℝ))) / γ + 2 :=
      hbase
    _ ≤ 4 * (B : ℝ) * (1 / (2 * (A : ℝ))) +
          2 * (B : ℝ) * γ +
          4 * (1 / (2 * (A : ℝ))) / γ + 2 := by
      linarith
    _ = 2 * (B : ℝ) / (A : ℝ) + 2 * (B : ℝ) * γ +
        2 / ((A : ℝ) * γ) + 2 := by
      field_simp [hApos.ne', hγ.ne']
      ring

end

end ZeroFreeRegion.VinogradovKorobov
