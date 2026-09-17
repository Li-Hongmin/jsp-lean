import JSP000625Comparison
import JSP000625Kernel

noncomputable section
open MeasureTheory Filter Topology AddCircle
namespace JSP000625

lemma tendsto_square_left_one :
    Tendsto (fun r : ℝ => r ^ 2) (𝓝[<] 1) (𝓝[<] 1) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · have hh : ContinuousAt (fun r : ℝ => r ^ 2) 1 := by fun_prop
    simpa using hh.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with r hr hr0
    change r ^ 2 < 1
    change r < 1 at hr
    nlinarith

lemma tendsto_normalized_window_lower {A : Set ℕ} {c C : ℝ}
    (h : ∀ N : ℕ, |(cumulative A N : ℝ) - c * (N : ℝ)| ≤ C) (m : ℕ) :
    Tendsto (fun r : ℝ => Real.sqrt (1 - r ^ 2) *
      (realSeries A (r ^ 2) * ∑ j ∈ Finset.range m, (r ^ 2) ^ j))
      (𝓝[<] 1) (𝓝 ((m : ℝ) * Real.sqrt c)) := by
  have hF := (tendsto_normalized_realSeries h).comp tendsto_square_left_one
  have hH : Tendsto (fun r : ℝ => ∑ j ∈ Finset.range m, (r ^ 2) ^ j)
      (𝓝[<] 1) (𝓝 (m : ℝ)) := by
    have hh : ContinuousAt (fun r : ℝ => ∑ j ∈ Finset.range m, (r ^ 2) ^ j) 1 := by fun_prop
    simpa using hh.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [Function.comp_def, mul_assoc, mul_comm (Real.sqrt c)] using hF.mul hH

/-- The final numerical contradiction in the finite-window proof. -/
lemma impossible_window_bounds {c C : ℝ} (hc : 0 < c) (_hC : 0 ≤ C)
    (h : ∀ m : ℕ, (m : ℝ) * Real.sqrt c ≤ 2 * C * Real.sqrt m) : False := by
  obtain ⟨m, hm⟩ := exists_nat_gt (4 * C ^ 2 / c + 1)
  have hpos : 0 < (m : ℝ) := by
    have : 0 ≤ 4 * C ^ 2 / c := by positivity
    linarith
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ (m : ℝ) * Real.sqrt c) (h m)
  have hsc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hsm : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt (by positivity)
  have hm' : 4 * C ^ 2 < (m : ℝ) * c := by
    have := (div_lt_iff₀ hc).mp (show 4 * C ^ 2 / c < (m : ℝ) by linarith)
    linarith
  have hs : (m : ℝ) ^ 2 * c ≤ 4 * C ^ 2 * (m : ℝ) := by
    calc
      (m : ℝ) ^ 2 * c = (m : ℝ) * Real.sqrt c * ((m : ℝ) * Real.sqrt c) := by
        nlinarith only [congrArg (fun x : ℝ => (m : ℝ) ^ 2 * x) hsc]
      _ ≤ 2 * C * Real.sqrt (m : ℝ) * (2 * C * Real.sqrt (m : ℝ)) := hsq
      _ = 4 * C ^ 2 * (m : ℝ) := by nlinarith only [congrArg (fun x : ℝ => 4 * C ^ 2 * x) hsm]
  nlinarith [mul_pos hpos (sub_pos.mpr hm')]

/-- A normalized Newman estimate for all window lengths contradicts a positive slope. -/
lemma contradiction_of_newman_estimate {A : Set ℕ} {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (h : ∀ N : ℕ, |(cumulative A N : ℝ) - c * (N : ℝ)| ≤ C)
    (hest : ∀ m : ℕ, ∀ᶠ r : ℝ in 𝓝[<] 1,
      Real.sqrt (1 - r ^ 2) *
        (realSeries A (r ^ 2) * ∑ j ∈ Finset.range m, (r ^ 2) ^ j) ≤
      c * (m : ℝ) ^ 2 * (Real.sqrt (1 - r ^ 2) *
        ∫ x : Circle, 1 / ‖1 - (r : ℂ) * fourier 1 x‖ ∂circleMeasure) +
      2 * C * Real.sqrt (m : ℝ)) : False := by
  apply impossible_window_bounds hc hC
  intro m
  have hu := (tendsto_normalized_kernel_integral.const_mul (c * (m : ℝ) ^ 2)).add_const
    (2 * C * Real.sqrt (m : ℝ))
  have hl := tendsto_normalized_window_lower h m
  have := le_of_tendsto_of_tendsto hl hu (hest m)
  simpa using this

#print axioms impossible_window_bounds
#print axioms contradiction_of_newman_estimate
end JSP000625
