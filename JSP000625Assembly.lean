import JSP000625Bridge
import JSP000625Upper
import JSP000625Finish

noncomputable section
open MeasureTheory Filter Topology AddCircle
namespace JSP000625

lemma radialSet_apply (A : Set ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x : Circle) :
    fourierSeries (radialSetCoefficient A (r : ℂ)) x =
      powerSeries (indicatorCoefficient A) ((r : ℂ) * fourier 1 x) :=
  fourierSeries_radial_apply (boundedCoefficients_indicator A) hr hr1 x

lemma windowCount_sum_eq (A : Set ℕ) (m : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑' n, (windowCount A m n : ℝ) * r ^ (2 * n)) =
      realSeries A (r ^ 2) * ∑ j ∈ Finset.range m, (r ^ 2) ^ j := by
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hz2 : ‖((r ^ 2 : ℝ) : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, abs_of_nonneg (sq_nonneg r)] using hr2
  have heq := congrArg (fun f : C(Circle, ℂ) => f 0) (fourierSeries_mul_window A m hz2)
  simp only [ContinuousMap.mul_apply] at heq
  rw [radialSet_apply A (sq_nonneg r) hr2,
    fourierSeries_radialWindow_apply m (sq_nonneg r) hr2,
    fourier_eval_zero, mul_one, ← realSeries_complex] at heq
  rw [fourierSeries_apply (summable_norm_windowCount_radial A m hz2)] at heq
  simp only [fourier_eval_zero, mul_one] at heq
  apply Complex.ofReal_injective
  push_cast
  convert heq.symm using 1
  · congr 1
    funext n
    rw [pow_mul]
    simp
  · simp

lemma window_lower (A : Set ℕ) (m : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    realSeries A (r ^ 2) * (∑ j ∈ Finset.range m, (r ^ 2) ^ j) ≤
      ∫ x, ‖(fourierSeries (radialSetCoefficient A (r : ℂ)) *
        fourierSeries (radialWindowCoefficient m (r : ℂ))) x‖ ^ 2 ∂circleMeasure := by
  rw [← windowCount_sum_eq A m hr hr1]
  exact tsum_windowCount_le_parseval A m hr hr1

/-- Cancellation of the radial blowup in the Cauchy--Schwarz error term. -/
lemma normalized_sqrt_bound {d X C : ℝ} (hd : 0 < d) (_hX : 0 ≤ X) (hC : 0 ≤ C)
    (h : X ≤ C ^ 2 / d) : Real.sqrt d * Real.sqrt X ≤ C := by
  rw [← Real.sqrt_mul hd.le]
  apply (Real.sqrt_le_left hC).2
  have := (le_div_iff₀ hd).mp h
  nlinarith

/-- Newman's finite-window estimate after normalization. -/
lemma normalized_newman_estimate {A : Set ℕ} {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (h : ∀ N : ℕ, |(cumulative A N : ℝ) - c * (N : ℝ)| ≤ C)
    (m : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Real.sqrt (1 - r ^ 2) *
      (realSeries A (r ^ 2) * ∑ j ∈ Finset.range m, (r ^ 2) ^ j) ≤
    c * (m : ℝ) ^ 2 * (Real.sqrt (1 - r ^ 2) *
      ∫ x : Circle, 1 / ‖1 - (r : ℂ) * fourier 1 x‖ ∂circleMeasure) +
    2 * C * Real.sqrt (m : ℝ) := by
  let F := fourierSeries (radialSetCoefficient A (r : ℂ))
  let E := fourierSeries (fun n => cumulativeError A c n * (r : ℂ) ^ n)
  let H := fourierSeries (radialWindowCoefficient m (r : ℂ))
  let G := fourierSeries (fun n : ℕ => (r : ℂ) ^ n)
  have hpoint : ∀ x, ‖(F * H) x‖ ^ 2 ≤ c * (m : ℝ) ^ 2 * ‖G x‖ +
      2 * ‖E x‖ * ‖H x‖ := by
    intro x
    have hz : ‖(r : ℂ) * fourier 1 x‖ < 1 := by
      simpa [norm_mul, fourier_apply, Complex.norm_real, abs_of_nonneg hr] using hr1
    have hp := newman_pointwise hc.le hz.le (powerSeries_indicator_sq_eq_main_add_error h hz) m
    simpa only [F, E, H, G, ContinuousMap.mul_apply, radialSet_apply A hr hr1,
      fourierSeries_radialWindow_apply m hr hr1,
      fourierSeries_radial_apply (boundedCoefficients_cumulativeError h) hr hr1,
      circle_geometric_eq hr hr1] using hp
  have hu := newman_integral_upper F E H G c m hpoint
  have hl := window_lower A m hr hr1
  have hd : 0 < 1 - r ^ 2 := by nlinarith
  have he := cumulativeError_fourier_l2_le h hr hr1
  have hh := radialWindow_fourier_l2_le m hr hr1
  have hEnonneg : 0 ≤ ∫ x, ‖E x‖ ^ 2 ∂circleMeasure := integral_nonneg (fun x => sq_nonneg _)
  have hE := normalized_sqrt_bound hd hEnonneg hC he
  have hH := Real.sqrt_le_sqrt hh
  have hG : (∫ x, ‖G x‖ ∂circleMeasure) =
      ∫ x : Circle, 1 / ‖1 - (r : ℂ) * fourier 1 x‖ ∂circleMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      simp only [G, circle_geometric_eq hr hr1, norm_inv, one_div])
  have hupper := mul_le_mul_of_nonneg_left (hl.trans hu) (Real.sqrt_nonneg (1 - r ^ 2))
  have herr : Real.sqrt (1 - r ^ 2) *
      (2 * Real.sqrt (∫ x, ‖E x‖ ^ 2 ∂circleMeasure) *
        Real.sqrt (∫ x, ‖H x‖ ^ 2 ∂circleMeasure)) ≤ 2 * C * Real.sqrt (m : ℝ) := by
    calc
      _ = 2 * (Real.sqrt (1 - r ^ 2) * Real.sqrt (∫ x, ‖E x‖ ^ 2 ∂circleMeasure)) *
          Real.sqrt (∫ x, ‖H x‖ ^ 2 ∂circleMeasure) := by ring
      _ ≤ 2 * C * Real.sqrt (m : ℝ) := by gcongr
  rw [hG] at hupper
  nlinarith

#print axioms normalized_newman_estimate
end JSP000625
