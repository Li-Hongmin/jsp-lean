import Mathlib
set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory AddCircle
open scoped ComplexConjugate
namespace JSP000625

abbrev Circle := AddCircle (1 : ℝ)
abbrev circleMeasure : Measure Circle := haarAddCircle

/-- Fourier coefficient as a continuous linear functional on continuous circle functions. -/
def coeffCLM (k : ℤ) : C(Circle, ℂ) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).comp
    (fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousMap.toLp 2 circleMeasure ℂ))

lemma coeffCLM_apply (f : C(Circle, ℂ)) (k : ℤ) :
    coeffCLM k f = fourierCoeff f k := by
  change fourierBasis.repr (ContinuousMap.toLp 2 circleMeasure ℂ f) k = _
  rw [fourierBasis_repr, fourierCoeff_toLp]

lemma summable_fourier {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) :
    Summable (fun n => a n • (fourier (n : ℤ) : C(Circle, ℂ))) := by
  apply ha.of_norm_bounded
  intro n
  simp only [norm_smul, fourier_norm, mul_one, le_refl]

/-- The absolutely convergent Fourier series with nonnegative frequencies. -/
def fourierSeries (a : ℕ → ℂ) : C(Circle, ℂ) :=
  ∑' n, a n • fourier (n : ℤ)

lemma fourierSeries_apply {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) (x : Circle) :
    fourierSeries a x = ∑' n, a n * fourier (n : ℤ) x := by
  rw [fourierSeries, ← ContinuousMap.tsum_apply (summable_fourier ha)]
  rfl

lemma fourierCoeff_series {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) (k : ℤ) :
    fourierCoeff (fourierSeries a) k =
      ∑' n : ℕ, if (n : ℤ) = k then a n else 0 := by
  rw [← coeffCLM_apply, fourierSeries, (coeffCLM k).map_tsum (summable_fourier ha)]
  congr 1
  funext n
  rw [map_smul, coeffCLM_apply]
  simp only [fourierCoeff_fourier, Pi.single_apply, smul_eq_mul]
  split_ifs with h <;> simp_all

lemma fourierCoeff_series_nat {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) (k : ℕ) :
    fourierCoeff (fourierSeries a) (k : ℤ) = a k := by
  rw [fourierCoeff_series ha]
  simp

lemma fourierCoeff_series_neg {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖))
    {k : ℤ} (hk : k < 0) : fourierCoeff (fourierSeries a) k = 0 := by
  rw [fourierCoeff_series ha]
  have hne : ∀ n : ℕ, (n : ℤ) ≠ k := by intro n; omega
  simp [hne]

lemma parseval_continuous (f : C(Circle, ℂ)) :
    ∑' k : ℤ, ‖fourierCoeff f k‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂circleMeasure := by
  have h := tsum_sq_fourierCoeff (ContinuousMap.toLp 2 circleMeasure ℂ f)
  simp_rw [fourierCoeff_toLp] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp circleMeasure (𝕜 := ℂ) (p := 2) f] with x hx
  rw [hx]

/-- Parseval for an absolutely convergent power series, expressed on the unit circle. -/
lemma parseval_series {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) :
    ∫ x, ‖fourierSeries a x‖ ^ 2 ∂circleMeasure = ∑' n, ‖a n‖ ^ 2 := by
  rw [← parseval_continuous]
  have h := (Nat.cast_injective (R := ℤ)).tsum_eq
    (f := fun k : ℤ => ‖fourierCoeff (fourierSeries a) k‖ ^ 2) ?_
  · simpa only [fourierCoeff_series_nat ha] using h.symm
  · intro k hk
    have hk0 : 0 ≤ k := by
      by_contra h
      simp [fourierCoeff_series_neg ha (by omega : k < 0)] at hk
    exact ⟨k.toNat, Int.toNat_of_nonneg hk0⟩


/-- Multiplication of absolutely convergent Fourier series is Cauchy convolution. -/
lemma fourierSeries_mul {a b : ℕ → ℂ}
    (ha : Summable (fun n => ‖a n‖)) (hb : Summable (fun n => ‖b n‖)) :
    fourierSeries a * fourierSeries b =
      fourierSeries (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2) := by
  unfold fourierSeries
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm]
  · congr 1
    funext n
    dsimp only
    ext x
    simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hpn : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [← hpn, Nat.cast_add, fourier_add]
    ring
  · simpa only [norm_smul, fourier_norm, mul_one] using ha
  · simpa only [norm_smul, fourier_norm, mul_one] using hb

/-- Cauchy–Schwarz for continuous functions on the probability circle. -/
lemma circle_cauchy_schwarz (f g : C(Circle, ℂ)) :
    (∫ x, ‖f x‖ * ‖g x‖ ∂circleMeasure) ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂circleMeasure) *
      Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂circleMeasure) := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using f.memLp (p := 2) circleMeasure ℂ)
    (by simpa using g.memLp (p := 2) circleMeasure ℂ)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h

#print axioms parseval_series
#print axioms fourierSeries_mul
#print axioms circle_cauchy_schwarz
end JSP000625
