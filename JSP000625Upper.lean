import JSP000625Fourier

noncomputable section
open MeasureTheory AddCircle
namespace JSP000625

/-- Integrability of every continuous scalar function on the compact circle. -/
lemma integrable_circle {f : Circle → ℝ} (hf : Continuous f) :
    Integrable f circleMeasure :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Pointwise estimate from Newman's equations (12)--(14). -/
lemma newman_pointwise {F E z : ℂ} {c : ℝ} (hc : 0 ≤ c) (hz : ‖z‖ ≤ 1)
    (hid : F ^ 2 = (c : ℂ) * z / (1 - z) + (1 - z) * E) (m : ℕ) :
    ‖F * (∑ j ∈ Finset.range m, z ^ j)‖ ^ 2 ≤
      c * (m : ℝ) ^ 2 * ‖(1 - z)⁻¹‖ +
        2 * ‖E‖ * ‖∑ j ∈ Finset.range m, z ^ j‖ := by
  let H := ∑ j ∈ Finset.range m, z ^ j
  have hH : ‖H‖ ≤ m := by
    calc
      ‖H‖ ≤ ∑ j ∈ Finset.range m, ‖z ^ j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg z) hz
      _ = m := by simp
  have hprod : ‖(1 - z) * H‖ ≤ 2 := by
    rw [mul_comm, geom_sum_mul_neg]
    calc
      ‖1 - z ^ m‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ m‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_one, norm_pow]
        have := pow_le_one₀ (norm_nonneg z) hz (n := m)
        linarith
  have hmain : ‖(c : ℂ) * z / (1 - z) * H ^ 2‖ ≤
      c * (m : ℝ) ^ 2 * ‖(1 - z)⁻¹‖ := by
    simp only [div_eq_mul_inv, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hc]
    calc
      c * ‖z‖ * ‖(1 - z)⁻¹‖ * ‖H‖ ^ 2 ≤
          c * 1 * ‖(1 - z)⁻¹‖ * (m : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  calc
    ‖F * H‖ ^ 2 = ‖F ^ 2 * H ^ 2‖ := by simp [norm_pow, mul_pow]
    _ = ‖(c : ℂ) * z / (1 - z) * H ^ 2 + E * ((1 - z) * H) * H‖ := by
      rw [hid]
      congr 1
      ring
    _ ≤ ‖(c : ℂ) * z / (1 - z) * H ^ 2‖ + ‖E * ((1 - z) * H) * H‖ :=
      norm_add_le _ _
    _ ≤ c * (m : ℝ) ^ 2 * ‖(1 - z)⁻¹‖ + 2 * ‖E‖ * ‖H‖ := by
      rw [norm_mul, norm_mul]
      have herror : ‖E‖ * ‖(1 - z) * H‖ * ‖H‖ ≤ 2 * ‖E‖ * ‖H‖ := by
        nlinarith [mul_le_mul_of_nonneg_left hprod (norm_nonneg E), norm_nonneg H]
      rw [norm_mul] at hmain
      exact add_le_add hmain (by simpa only [norm_mul] using herror)

/-- Integrated Newman estimate, with the error term bounded by Cauchy--Schwarz. -/
lemma newman_integral_upper (F E H G : C(Circle, ℂ)) (c : ℝ) (m : ℕ)
    (hpoint : ∀ x, ‖(F * H) x‖ ^ 2 ≤
      c * (m : ℝ) ^ 2 * ‖G x‖ + 2 * ‖E x‖ * ‖H x‖) :
    (∫ x, ‖(F * H) x‖ ^ 2 ∂circleMeasure) ≤
      c * (m : ℝ) ^ 2 * (∫ x, ‖G x‖ ∂circleMeasure) +
      2 * Real.sqrt (∫ x, ‖E x‖ ^ 2 ∂circleMeasure) *
        Real.sqrt (∫ x, ‖H x‖ ^ 2 ∂circleMeasure) := by
  calc
    (∫ x, ‖(F * H) x‖ ^ 2 ∂circleMeasure) ≤
        ∫ x, (c * (m : ℝ) ^ 2 * ‖G x‖ + 2 * ‖E x‖ * ‖H x‖) ∂circleMeasure := by
      apply integral_mono (integrable_circle (by fun_prop))
        (integrable_circle (by fun_prop)) hpoint
    _ = c * (m : ℝ) ^ 2 * (∫ x, ‖G x‖ ∂circleMeasure) +
        2 * (∫ x, ‖E x‖ * ‖H x‖ ∂circleMeasure) := by
      rw [integral_add (integrable_circle (by fun_prop))
        (integrable_circle (by fun_prop))]
      simp_rw [mul_assoc (2 : ℝ)]
      rw [integral_const_mul, integral_const_mul]
    _ ≤ _ := by
      have h := circle_cauchy_schwarz E H
      nlinarith

#print axioms newman_pointwise
#print axioms newman_integral_upper
end JSP000625
