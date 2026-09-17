import JSP000625Counting
import JSP000625Fourier

/-!
Finite-window coefficient identities for the elementary Erdős--Fuchs
Parseval argument.
-/

noncomputable section

open MeasureTheory AddCircle

namespace JSP000625

/-- Complex-valued characteristic coefficient of a set. -/
noncomputable def setIndicator (A : Set ℕ) (n : ℕ) : ℂ := by
  classical
  exact if n ∈ A then 1 else 0

/-- The complex `0`-`1` coefficient sequence of the length-`m` window. -/
noncomputable def windowIndicator (m n : ℕ) : ℂ :=
  if n < m then 1 else 0

/-- Coefficients of the set series restricted to the circle of radius `z`. -/
def radialSetCoefficient (A : Set ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  setIndicator A n * z ^ n

/-- Coefficients of the length-`m` window series on the circle of radius `z`. -/
def radialWindowCoefficient (m : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  windowIndicator m n * z ^ n

theorem summable_norm_radialSetCoefficient (A : Set ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n => ‖radialSetCoefficient A z n‖) := by
  have hg : Summable (fun n : ℕ => ‖z‖ ^ n) :=
    summable_geometric_of_norm_lt_one (by simpa using hz)
  refine hg.of_norm_bounded fun n => ?_
  rw [norm_norm, radialSetCoefficient, norm_mul, norm_pow]
  apply mul_le_of_le_one_left (pow_nonneg (norm_nonneg z) n)
  simp only [setIndicator]
  split <;> simp

theorem summable_norm_radialWindowCoefficient (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n => ‖radialWindowCoefficient m z n‖) := by
  have hg : Summable (fun n : ℕ => ‖z‖ ^ n) :=
    summable_geometric_of_norm_lt_one (by simpa using hz)
  refine hg.of_norm_bounded fun n => ?_
  rw [norm_norm, radialWindowCoefficient, norm_mul, norm_pow]
  apply mul_le_of_le_one_left (pow_nonneg (norm_nonneg z) n)
  simp only [windowIndicator]
  split <;> simp

/-- The number of decompositions `n = a + j` with `a ∈ A` and `j < m`.
The summation coordinate here is `a`; this is equivalent to summing over
`j < m` and testing `n-j ∈ A`. -/
noncomputable def windowCount (A : Set ℕ) (m n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter fun a => a ∈ A ∧ n - a < m).card

/-- Multiplying the set coefficients by a finite window produces the natural
coefficient `windowCount`, together with the common radial factor `z^n`. -/
theorem radial_convolution_eq_windowCount (A : Set ℕ) (m n : ℕ) (z : ℂ) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      radialSetCoefficient A z p.1 * radialWindowCoefficient m z p.2) =
      (windowCount A m n : ℂ) * z ^ n := by
  classical
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [windowCount, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr (by simp [Nat.succ_eq_add_one])
  intro a ha
  have han : a ≤ n := Nat.le_of_lt_succ (by simpa using ha)
  simp only [radialSetCoefficient, radialWindowCoefficient, setIndicator,
    windowIndicator]
  by_cases hA : a ∈ A <;> by_cases hm : n - a < m
  · simp only [hA, hm, if_pos, one_mul, Nat.cast_one, true_and]
    rw [← pow_add, Nat.add_sub_of_le han]
  · simp [hA, hm]
  · simp [hA, hm]
  · simp [hA, hm]

/-- The product of the two boundary Fourier series has the window counts as
its radial coefficients. -/
theorem fourierSeries_mul_window (A : Set ℕ) (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    fourierSeries (radialSetCoefficient A z) *
        fourierSeries (radialWindowCoefficient m z) =
      fourierSeries (fun n => (windowCount A m n : ℂ) * z ^ n) := by
  rw [fourierSeries_mul (summable_norm_radialSetCoefficient A hz)
    (summable_norm_radialWindowCoefficient m hz)]
  congr 1
  funext n
  exact radial_convolution_eq_windowCount A m n z

theorem summable_norm_windowCount_radial (A : Set ℕ) (m : ℕ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    Summable (fun n => ‖(windowCount A m n : ℂ) * z ^ n‖) := by
  have hconv := summable_norm_sum_mul_antidiagonal_of_summable_norm
    (summable_norm_radialSetCoefficient A hz)
    (summable_norm_radialWindowCoefficient m hz)
  exact hconv.congr fun n =>
    congrArg norm (radial_convolution_eq_windowCount A m n z)

theorem summable_sq_norm_windowCount_radial (A : Set ℕ) (m : ℕ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    Summable (fun n => ‖(windowCount A m n : ℂ) * z ^ n‖ ^ 2) := by
  have hnorm := summable_norm_windowCount_radial A m hz
  have htend := hnorm.tendsto_atTop_zero
  have hone : ∀ᶠ n in Filter.atTop,
      ‖(windowCount A m n : ℂ) * z ^ n‖ < 1 :=
    (tendsto_order.1 htend).2 1 zero_lt_one
  refine Summable.of_norm_bounded_eventually_nat hnorm ?_
  filter_upwards [hone] with n hn
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg ((windowCount A m n : ℂ) * z ^ n)]

/-- Parseval converts the squared boundary norm of the windowed product into
the exact sum of squares of the natural window coefficients. -/
theorem parseval_window_product (A : Set ℕ) (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    (∫ x, ‖(fourierSeries (radialSetCoefficient A z) *
        fourierSeries (radialWindowCoefficient m z)) x‖ ^ 2 ∂circleMeasure) =
      ∑' n, ‖(windowCount A m n : ℂ) * z ^ n‖ ^ 2 := by
  have hcount := summable_norm_windowCount_radial A m hz
  rw [fourierSeries_mul_window A m hz]
  exact parseval_series hcount

/-- Since `windowCount` is a natural number, squaring it can only increase it.
This is the pointwise inequality behind the lower Parseval estimate. -/
theorem windowCount_radial_le_sq (A : Set ℕ) (m n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (windowCount A m n : ℝ) * r ^ (2 * n) ≤
      ‖(windowCount A m n : ℂ) * (r : ℂ) ^ n‖ ^ 2 := by
  rw [norm_mul, norm_natCast, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, mul_comm 2 n, pow_mul]
  have hb : (windowCount A m n : ℝ) ≤
      (windowCount A m n : ℝ) * (windowCount A m n : ℝ) := by
    exact_mod_cast Nat.le_mul_self (windowCount A m n)
  have hx : 0 ≤ (r ^ n) ^ 2 := sq_nonneg _
  nlinarith

/-- The scalar lower Parseval bound.  Its left side is the Cauchy-product
coefficient sum; a separate Cauchy-product identity can rewrite it as the set
series at `r²` times the finite geometric window. -/
theorem tsum_windowCount_le_parseval (A : Set ℕ) (m : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n, (windowCount A m n : ℝ) * r ^ (2 * n)) ≤
      ∫ x, ‖(fourierSeries (radialSetCoefficient A (r : ℂ)) *
        fourierSeries (radialWindowCoefficient m (r : ℂ))) x‖ ^ 2 ∂circleMeasure := by
  have hz : ‖(r : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hsquare := summable_sq_norm_windowCount_radial A m hz
  have hlower : Summable (fun n => (windowCount A m n : ℝ) * r ^ (2 * n)) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0 _))
      (fun n => windowCount_radial_le_sq A m n hr0) hsquare
  calc
    (∑' n, (windowCount A m n : ℝ) * r ^ (2 * n)) ≤
        ∑' n, ‖(windowCount A m n : ℂ) * (r : ℂ) ^ n‖ ^ 2 :=
      Summable.tsum_le_tsum
        (fun n => windowCount_radial_le_sq A m n hr0) hlower hsquare
    _ = ∫ x, ‖(fourierSeries (radialSetCoefficient A (r : ℂ)) *
          fourierSeries (radialWindowCoefficient m (r : ℂ))) x‖ ^ 2 ∂circleMeasure :=
      (parseval_window_product A m hz).symm

end JSP000625
