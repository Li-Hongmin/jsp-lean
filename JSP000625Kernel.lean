import JSP000625Fourier

noncomputable section
open MeasureTheory Filter Topology AddCircle
namespace JSP000625

/-- On a finite measure space, bounded second moments and almost-everywhere convergence
    to zero imply convergence of the first moments. The proof uses bounded truncations. -/
lemma tendsto_integral_of_sq_bound {ι α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → α → ℝ}
    (hint : ∀ᶠ i in l, Integrable (f i) μ)
    (hsqint : ∀ᶠ i in l, Integrable (fun x => f i x ^ 2) μ)
    (hnonneg : ∀ᶠ i in l, ∀ x, 0 ≤ f i x)
    (hbound : ∀ᶠ i in l, ∫ x, f i x ^ 2 ∂μ ≤ 1)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, f i x ∂μ) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hnonneg] with i hi
    exact ha.trans_le (integral_nonneg hi)
  · intro b hb
    let K : ℝ := 2 / b
    have hK : 0 < K := div_pos (by norm_num) hb
    have htrunc : Tendsto (fun i => ∫ x, min (f i x) K ∂μ) l (𝓝 0) := by
      have h := tendsto_integral_filter_of_norm_le_const
        (μ := μ) (l := l) (F := fun i x => min (f i x) K) (f := fun _ => (0 : ℝ)) ?_ ?_ ?_
      · simpa using h
      · filter_upwards [hint] with i hi
        exact hi.aestronglyMeasurable.inf aestronglyMeasurable_const
      · refine ⟨K, ?_⟩
        filter_upwards [hnonneg] with i hi
        exact Filter.Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (le_min (hi x) hK.le)]
          exact min_le_right _ _
      · filter_upwards [hlim] with x hx
        simpa [min_eq_left hK.le] using hx.min (tendsto_const_nhds (x := K))
    have htruncsmall := (tendsto_order.1 htrunc).2 (b / 2) (by linarith)
    filter_upwards [hint, hsqint, hnonneg, hbound, htruncsmall] with i hi hsi hni hbi hti
    have hmini : Integrable (fun x => min (f i x) K) μ := hi.inf (integrable_const K)
    have hpoint : ∀ x, f i x ≤ min (f i x) K + f i x ^ 2 / K := by
      intro x
      by_cases hx : f i x ≤ K
      · rw [min_eq_left hx]
        exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hK.le)
      · rw [min_eq_right (le_of_not_ge hx)]
        have hh : f i x ≤ f i x ^ 2 / K := by
          apply (le_div_iff₀ hK).2
          nlinarith [hni x]
        linarith
    have hh := integral_mono hi (hmini.add (hsi.div_const K)) hpoint
    simp only [Pi.add_apply] at hh
    rw [integral_add hmini (hsi.div_const K), integral_div] at hh
    have hbK : 1 / K = b / 2 := by dsimp [K]; field_simp
    have hs : (∫ x, f i x ^ 2 ∂μ) / K ≤ b / 2 := by
      rw [← hbK]
      exact div_le_div_of_nonneg_right hbi hK.le
    linarith

lemma fourier_nat_pow (n : ℕ) (x : Circle) :
    fourier (n : ℤ) x = (fourier 1 x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

lemma circle_geometric_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ‖(r : ℂ) ^ n‖) := by
  simpa [norm_pow, Complex.norm_real, abs_of_nonneg hr] using
    summable_geometric_of_lt_one hr hr1

lemma circle_geometric_eq {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x : Circle) :
    fourierSeries (fun n : ℕ => (r : ℂ) ^ n) x =
      (1 - (r : ℂ) * fourier 1 x)⁻¹ := by
  rw [fourierSeries_apply (circle_geometric_summable hr hr1)]
  simp_rw [fourier_nat_pow, ← mul_pow]
  apply tsum_geometric_of_norm_lt_one
  simpa [norm_mul, fourier_apply, Complex.norm_real, abs_of_nonneg hr] using hr1

lemma kernel_denom_ne_zero {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x : Circle) :
    1 - (r : ℂ) * fourier 1 x ≠ 0 := by
  intro h
  have hn := congrArg norm (sub_eq_zero.mp h)
  simp [fourier_apply, Complex.norm_real, abs_of_nonneg hr] at hn
  linarith

lemma kernel_continuous {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun x : Circle => 1 / ‖1 - (r : ℂ) * fourier 1 x‖) := by
  apply Continuous.div continuous_const
  · fun_prop
  · intro x
    exact norm_ne_zero_iff.mpr (kernel_denom_ne_zero hr hr1 x)

lemma kernel_integral_sq {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫ x : Circle, (1 / ‖1 - (r : ℂ) * fourier 1 x‖) ^ 2 ∂circleMeasure) =
      1 / (1 - r ^ 2) := by
  have h := parseval_series (circle_geometric_summable hr hr1)
  simp_rw [circle_geometric_eq hr hr1, norm_inv, ← one_div] at h
  rw [h]
  simp_rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    ← pow_mul, mul_comm _ 2, pow_mul]
  simpa only [one_div] using tsum_geometric_of_lt_one (sq_nonneg r) (by nlinarith : r ^ 2 < 1)

/-- The reciprocal Cauchy kernel has negligible first moment on its L² scale. -/
theorem tendsto_normalized_kernel_integral :
    Tendsto (fun r : ℝ => Real.sqrt (1 - r ^ 2) *
      ∫ x : Circle, 1 / ‖1 - (r : ℂ) * fourier 1 x‖ ∂circleMeasure)
      (𝓝[<] 1) (𝓝 0) := by
  letI : Nontrivial Circle := ⟨⟨((1 / 2 : ℝ) : Circle), 0, by
    intro h
    have h0 := (AddCircle.coe_eq_zero_iff_of_mem_Ico (by norm_num : (1 / 2 : ℝ) ∈ Set.Ico 0 1)).mp h
    norm_num at h0⟩⟩
  have hrange : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 ≤ r ∧ r < 1 := by
    filter_upwards [(eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds, eventually_mem_nhdsWithin] with r hr hr1
    exact ⟨hr.le, hr1⟩
  let f : ℝ → Circle → ℝ := fun r x =>
    Real.sqrt (1 - r ^ 2) * (1 / ‖1 - (r : ℂ) * fourier 1 x‖)
  have hc : ∀ r : ℝ, 0 ≤ r → r < 1 → Continuous (f r) := by
    intro r hr hr1
    exact continuous_const.mul (kernel_continuous hr hr1)
  have hint : ∀ᶠ r in 𝓝[<] 1, Integrable (f r) circleMeasure := by
    filter_upwards [hrange] with r hr
    exact (hc r hr.1 hr.2).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hsqint : ∀ᶠ r in 𝓝[<] 1, Integrable (fun x => f r x ^ 2) circleMeasure := by
    filter_upwards [hrange] with r hr
    exact ((hc r hr.1 hr.2).pow 2).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hn : ∀ᶠ r in 𝓝[<] 1, ∀ x, 0 ≤ f r x := by
    exact Eventually.of_forall fun r x => mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hb : ∀ᶠ r in 𝓝[<] 1, ∫ x, f r x ^ 2 ∂circleMeasure ≤ 1 := by
    filter_upwards [hrange] with r hr
    have hs : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    simp only [f, mul_pow, integral_const_mul, Real.sq_sqrt hs.le,
      kernel_integral_sq hr.1 hr.2]
    exact le_of_eq (by field_simp)
  have hae : ∀ᵐ x : Circle ∂circleMeasure, x ≠ 0 := by
    rw [ae_iff]
    simp
  have ht : ∀ᵐ x ∂circleMeasure, Tendsto (fun r => f r x) (𝓝[<] 1) (𝓝 0) := by
    filter_upwards [hae] with x hx
    have hden : 1 - (1 : ℂ) * fourier 1 x ≠ 0 := by
      intro he
      have he' : AddCircle.toCircle x = AddCircle.toCircle (0 : Circle) := by
        apply _root_.Circle.coe_injective
        simpa [fourier_one] using (sub_eq_zero.mp he).symm
      exact hx (AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0) he')
    have hdenc : ContinuousAt (fun r : ℝ => ‖1 - (r : ℂ) * fourier 1 x‖) 1 := by
      fun_prop
    have hsqrt : Tendsto (fun r : ℝ => Real.sqrt (1 - r ^ 2)) (𝓝[<] 1) (𝓝 0) := by
      have hh : ContinuousAt (fun r : ℝ => Real.sqrt (1 - r ^ 2)) 1 := by fun_prop
      simpa using hh.tendsto.mono_left nhdsWithin_le_nhds
    have hinvc : ContinuousAt (fun r : ℝ => 1 / ‖1 - (r : ℂ) * fourier 1 x‖) 1 :=
      continuousAt_const.div hdenc (norm_ne_zero_iff.mpr hden)
    simpa [f] using hsqrt.mul (hinvc.tendsto.mono_left nhdsWithin_le_nhds)
  have result := tendsto_integral_of_sq_bound hint hsqint hn hb ht
  simpa only [f, integral_const_mul] using result

#print axioms tendsto_normalized_kernel_integral
end JSP000625
