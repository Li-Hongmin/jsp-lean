import JSP000625PowerSeries
import JSP000625Kernel
import JSP000625Window

/-!
Bridges between the ordinary power series and the boundary Fourier series.
-/

noncomputable section

open MeasureTheory AddCircle

namespace JSP000625

/-- Evaluating the radial Fourier series amounts to evaluating the ordinary power series at
`r · e(x)`. -/
theorem fourierSeries_radial_apply {u : ℕ → ℂ} (hu : BoundedCoefficients u)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x : Circle) :
    fourierSeries (fun n ↦ u n * (r : ℂ) ^ n) x =
      powerSeries u ((r : ℂ) * fourier 1 x) := by
  have hrnorm : ‖(r : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, abs_of_nonneg hr] using hr1
  rw [fourierSeries_apply (summable_norm_powerSeries_term hu hrnorm), powerSeries]
  apply tsum_congr
  intro n
  rw [fourier_nat_pow, mul_pow]
  ring

/-- Parseval bound for the bounded cumulative-error coefficients. -/
theorem cumulativeError_fourier_l2_le {A : Set ℕ} {c C r : ℝ}
    (h : ∀ N : ℕ, |(cumulative A N : ℝ) - c * (N : ℝ)| ≤ C)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫ x : Circle,
      ‖fourierSeries (fun n ↦ cumulativeError A c n * (r : ℂ) ^ n) x‖ ^ 2
        ∂circleMeasure) ≤ C ^ 2 / (1 - r ^ 2) := by
  have hrnorm : ‖(r : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, abs_of_nonneg hr] using hr1
  have hcoeff : Summable
      (fun n ↦ ‖cumulativeError A c n * (r : ℂ) ^ n‖) :=
    summable_norm_powerSeries_term (boundedCoefficients_cumulativeError h) hrnorm
  rw [parseval_series hcoeff]
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hmajor : Summable (fun n : ℕ ↦ C ^ 2 * (r ^ 2) ^ n) :=
    (summable_geometric_of_lt_one (sq_nonneg r) hr2).mul_left (C ^ 2)
  have hterm : ∀ n : ℕ,
      ‖cumulativeError A c n * (r : ℂ) ^ n‖ ^ 2 ≤ C ^ 2 * (r ^ 2) ^ n := by
    intro n
    have herr : ‖cumulativeError A c n‖ ≤ C := by
      rw [cumulativeError, Complex.norm_real, Real.norm_eq_abs]
      exact h n
    have hsquare : ‖cumulativeError A c n‖ ^ 2 ≤ C ^ 2 := by
      nlinarith [norm_nonneg (cumulativeError A c n)]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
      mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
    exact mul_le_mul_of_nonneg_right hsquare (pow_nonneg (sq_nonneg r) n)
  have hsummable : Summable
      (fun n : ℕ ↦ ‖cumulativeError A c n * (r : ℂ) ^ n‖ ^ 2) :=
    .of_nonneg_of_le (fun n ↦ sq_nonneg _) hterm hmajor
  calc
    (∑' n : ℕ, ‖cumulativeError A c n * (r : ℂ) ^ n‖ ^ 2) ≤
        ∑' n : ℕ, C ^ 2 * (r ^ 2) ^ n :=
      hsummable.tsum_le_tsum hterm hmajor
    _ = C ^ 2 * ∑' n : ℕ, (r ^ 2) ^ n := tsum_mul_left
    _ = C ^ 2 / (1 - r ^ 2) := by
      rw [tsum_geometric_of_lt_one (sq_nonneg r) hr2, div_eq_mul_inv]

/-- The radial length-`m` window has squared `L²` norm at most `m`. -/
theorem radialWindow_fourier_l2_le (m : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫ x : Circle, ‖fourierSeries (radialWindowCoefficient m (r : ℂ)) x‖ ^ 2
      ∂circleMeasure) ≤ (m : ℝ) := by
  have hrnorm : ‖(r : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, abs_of_nonneg hr] using hr1
  rw [parseval_series (summable_norm_radialWindowCoefficient m hrnorm)]
  rw [tsum_eq_sum (s := Finset.range m) (fun n hn ↦ by
    have hmn : ¬n < m := by simpa using hn
    simp [radialWindowCoefficient, windowIndicator, hmn])]
  calc
    (∑ n ∈ Finset.range m, ‖radialWindowCoefficient m (r : ℂ) n‖ ^ 2) ≤
        ∑ _n ∈ Finset.range m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnm : n < m := Finset.mem_range.mp hn
      simp only [radialWindowCoefficient, windowIndicator, if_pos hnm, one_mul,
        norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
      have hrpow : r ^ n ≤ 1 := pow_le_one₀ hr hr1.le
      nlinarith [pow_nonneg hr n]
    _ = (m : ℝ) := by simp

/-- The radial window Fourier series is the expected finite geometric sum. -/
theorem fourierSeries_radialWindow_apply (m : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r < 1) (x : Circle) :
    fourierSeries (radialWindowCoefficient m (r : ℂ)) x =
      ∑ n ∈ Finset.range m, ((r : ℂ) * fourier 1 x) ^ n := by
  have hrnorm : ‖(r : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, abs_of_nonneg hr] using hr1
  rw [fourierSeries_apply (summable_norm_radialWindowCoefficient m hrnorm)]
  rw [tsum_eq_sum (s := Finset.range m) (fun n hn ↦ by
    have hmn : ¬n < m := by simpa using hn
    simp [radialWindowCoefficient, windowIndicator, hmn])]
  apply Finset.sum_congr rfl
  intro n hn
  have hnm : n < m := Finset.mem_range.mp hn
  simp only [radialWindowCoefficient, windowIndicator, if_pos hnm, one_mul]
  rw [fourier_nat_pow, mul_pow]

end JSP000625
