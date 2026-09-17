import JSP000625PowerSeries
import JSP000625Fourier

noncomputable section
open MeasureTheory Filter Topology AddCircle
namespace JSP000625

/-- Real nonnegative set generating function. -/
def realSeries (A : Set ℕ) (r : ℝ) : ℝ := by
  classical
  exact ∑' n : ℕ, if n ∈ A then r ^ n else 0

lemma realSeries_nonneg (A : Set ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ realSeries A r := by
  classical
  apply tsum_nonneg
  intro n
  split_ifs <;> positivity

lemma realSeries_complex (A : Set ℕ) (r : ℝ) :
    (realSeries A r : ℂ) = powerSeries (indicatorCoefficient A) (r : ℂ) := by
  classical
  rw [realSeries, Complex.ofReal_tsum, powerSeries]
  apply tsum_congr
  intro n
  by_cases hn : n ∈ A <;> simp [indicatorCoefficient, hn]

/-- An error series with coefficient bound C has the elementary radial bound C/(1-r). -/
lemma powerSeries_bound {u : ℕ → ℂ} {C r : ℝ} (hu : ∀ n, ‖u n‖ ≤ C)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    ‖powerSeries u (r : ℂ)‖ ≤ C / (1 - r) := by
  have hz : ‖(r : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_nonneg hr] using hr1
  have hs := summable_norm_powerSeries_term ⟨C, hu⟩ hz
  calc
    ‖powerSeries u (r : ℂ)‖ ≤ ∑' n, ‖u n * (r : ℂ) ^ n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, C * r ^ n := by
      apply hs.tsum_le_tsum _ ((summable_geometric_of_lt_one hr hr1).mul_left C)
      intro n
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
      exact mul_le_mul_of_nonneg_right (hu n) (pow_nonneg hr n)
    _ = C / (1 - r) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr1]
      rfl

/-- Exact uniform radial error estimate, using c*r/(1-r). -/
lemma realSeries_sq_error {A : Set ℕ} {c C r : ℝ}
    (h : ∀ N : ℕ, |(cumulative A N : ℝ) - c * (N : ℝ)| ≤ C)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    |realSeries A r ^ 2 - c * r / (1 - r)| ≤ C := by
  have hz : ‖(r : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_nonneg hr] using hr1
  have hid := powerSeries_indicator_sq_eq_main_add_error h hz
  rw [← realSeries_complex] at hid
  have hbd := powerSeries_bound (u := cumulativeError A c) (C := C)
    (fun n => by
      change ‖(((cumulative A n : ℝ) - c * (n : ℝ) : ℝ) : ℂ)‖ ≤ C
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact h n) hr hr1
  have hpos : 0 < 1 - r := sub_pos.mpr hr1
  have heq : ‖((realSeries A r ^ 2 - c * r / (1 - r) : ℝ) : ℂ)‖ =
      (1 - r) * ‖powerSeries (cumulativeError A c) (r : ℂ)‖ := by
    push_cast
    rw [show (realSeries A r : ℂ) ^ 2 - (c : ℂ) * (r : ℂ) / (1 - (r : ℂ)) =
      (1 - (r : ℂ)) * powerSeries (cumulativeError A c) (r : ℂ) by linear_combination hid]
    rw [norm_mul]
    congr 1
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos]
  rw [Complex.norm_real, Real.norm_eq_abs] at heq
  rw [heq]
  calc
    _ ≤ (1 - r) * (C / (1 - r)) := mul_le_mul_of_nonneg_left hbd hpos.le
    _ = C := by field_simp

/-- The normalized square tends to the positive slope. -/
lemma tendsto_normalized_realSeries_sq {A : Set ℕ} {c C : ℝ}
    (h : ∀ N : ℕ, |(cumulative A N : ℝ) - c * (N : ℝ)| ≤ C) :
    Tendsto (fun r : ℝ => (1 - r) * realSeries A r ^ 2) (𝓝[<] 1) (𝓝 c) := by
  have hnear : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 ≤ r ∧ r < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r from
        (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)] with r hr hr0
    exact ⟨hr0.le, hr⟩
  have hbound : ∀ᶠ r : ℝ in 𝓝[<] 1,
      |(1 - r) * realSeries A r ^ 2 - c * r| ≤ C * (1 - r) := by
    filter_upwards [hnear] with r hr
    have hb := realSeries_sq_error h hr.1 hr.2
    have he : (1 - r) * realSeries A r ^ 2 - c * r =
        (1 - r) * (realSeries A r ^ 2 - c * r / (1 - r)) := by
      field_simp [ne_of_gt (sub_pos.mpr hr.2)]
    rw [he, abs_mul, abs_of_pos (sub_pos.mpr hr.2)]
    nlinarith [mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hr.2.le)]
  have hid : Tendsto (fun r : ℝ => r) (𝓝[<] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun r : ℝ => C * (1 - r)) (𝓝[<] 1) (𝓝 0) := by
    convert tendsto_const_nhds.mul (tendsto_const_nhds.sub hid) using 1; simp
  have hz : Tendsto (fun r : ℝ => (1 - r) * realSeries A r ^ 2 - c * r)
      (𝓝[<] 1) (𝓝 0) := by
    apply squeeze_zero_norm' hbound hlim
  have hc : Tendsto (fun _ : ℝ => c) (𝓝[<] 1) (𝓝 c) := tendsto_const_nhds
  have hh := hz.add (hc.mul hid)
  simpa using hh


/-- The normalized radial series has the square-root asymptotic. -/
lemma tendsto_normalized_realSeries {A : Set ℕ} {c C : ℝ}
    (h : ∀ N : ℕ, |(cumulative A N : ℝ) - c * (N : ℝ)| ≤ C) :
    Tendsto (fun r : ℝ => Real.sqrt (1 - r) * realSeries A r)
      (𝓝[<] 1) (𝓝 (Real.sqrt c)) := by
  have ht := (tendsto_normalized_realSeries_sq h).sqrt
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
    nhdsWithin_le_nhds] with r hr1 hr
  rw [Real.sqrt_mul (sub_nonneg.mpr (le_of_lt hr1))]
  rw [Real.sqrt_sq (realSeries_nonneg A hr.le)]

#print axioms realSeries_sq_error
#print axioms tendsto_normalized_realSeries_sq
end JSP000625
