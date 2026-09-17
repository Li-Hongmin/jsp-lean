import JSP000625Statement

/-!
Elementary power-series identities used in the bounded-error case of the
Erdős--Fuchs theorem.  Coefficients and the variable are complex so the same
lemmas can be used both on the real radius and on its boundary circle.
-/

namespace JSP000625

open scoped BigOperators
open Finset.HasAntidiagonal

/-- The ordinary generating function with coefficient sequence `u`. -/
noncomputable def powerSeries (u : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, u n * z ^ n

/-- A convenient pointwise formulation of bounded coefficients. -/
def BoundedCoefficients (u : ℕ → ℂ) : Prop :=
  ∃ M : ℝ, ∀ n, ‖u n‖ ≤ M

/-- Bounded coefficients give an absolutely convergent power series in the open unit disc. -/
theorem summable_norm_powerSeries_term {u : ℕ → ℂ} (hu : BoundedCoefficients u)
    {z : ℂ} (hz : ‖z‖ < 1) : Summable (fun n ↦ ‖u n * z ^ n‖) := by
  obtain ⟨M, hM⟩ := hu
  refine ((summable_norm_geometric_of_norm_lt_one hz).mul_left M).of_norm_bounded fun n ↦ ?_
  rw [norm_norm, norm_mul]
  exact mul_le_mul_of_nonneg_right (hM n) (norm_nonneg _)

/-- In particular, the defining complex series is summable. -/
theorem summable_powerSeries_term {u : ℕ → ℂ} (hu : BoundedCoefficients u)
    {z : ℂ} (hz : ‖z‖ < 1) : Summable (fun n ↦ u n * z ^ n) :=
  (summable_norm_powerSeries_term hu hz).of_norm

/-- A bounded coefficient sequence is bounded by the corresponding geometric series. -/
theorem norm_powerSeries_le {u : ℕ → ℂ} {M : ℝ} (hM : ∀ n, ‖u n‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖powerSeries u z‖ ≤ M / (1 - ‖z‖) := by
  have hleft : Summable (fun n ↦ ‖u n * z ^ n‖) :=
    summable_norm_powerSeries_term ⟨M, hM⟩ hz
  have hright : Summable (fun n : ℕ ↦ M * ‖z‖ ^ n) :=
    (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left M
  calc
    ‖powerSeries u z‖ ≤ ∑' n : ℕ, ‖u n * z ^ n‖ := by
      exact norm_tsum_le_tsum_norm hleft
    _ ≤ ∑' n : ℕ, M * ‖z‖ ^ n := hleft.tsum_le_tsum (fun n ↦ by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right (hM n) (pow_nonneg (norm_nonneg z) n)) hright
    _ = M * ∑' n : ℕ, ‖z‖ ^ n := tsum_mul_left
    _ = M / (1 - ‖z‖) := by
      rw [tsum_geometric_of_lt_one (norm_nonneg z) hz]
      rw [div_eq_mul_inv]

/-- Cauchy's product formula for two bounded coefficient sequences. -/
theorem powerSeries_mul {u v : ℕ → ℂ} (hu : BoundedCoefficients u)
    (hv : BoundedCoefficients v) {z : ℂ} (hz : ‖z‖ < 1) :
    powerSeries u z * powerSeries v z =
      ∑' n : ℕ, (∑ kl ∈ antidiagonal n, u kl.1 * v kl.2) * z ^ n := by
  rw [powerSeries, powerSeries]
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_powerSeries_term hu hz) (summable_norm_powerSeries_term hv hz)]
  apply tsum_congr
  intro n
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  rw [mem_antidiagonal] at hkl
  rw [← hkl, pow_add]
  ring

/-- The cumulative (prefix-sum) coefficient sequence. -/
def partialCoefficients (u : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), u k

/-- Prefix sums still define an absolutely convergent series in the open unit disc. -/
theorem summable_norm_partialCoefficients_term_of_summable {u : ℕ → ℂ} {z : ℂ}
    (hU : Summable (fun n ↦ ‖u n * z ^ n‖)) (hz : ‖z‖ < 1) :
    Summable (fun n ↦ ‖partialCoefficients u n * z ^ n‖) := by
  have hG : Summable (fun n : ℕ ↦ ‖z ^ n‖) :=
    summable_norm_geometric_of_norm_lt_one hz
  have hconv := summable_norm_sum_mul_range_of_summable_norm hU hG
  refine hconv.congr fun n ↦ ?_
  congr 1
  rw [partialCoefficients, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  calc
    u k * z ^ k * z ^ (n - k) = u k * (z ^ k * z ^ (n - k)) := by ring
    _ = u k * z ^ n := by rw [← pow_add, Nat.add_sub_of_le hkn]

/-- Prefix sums of bounded coefficients are absolutely summable in the open unit disc. -/
theorem summable_norm_partialCoefficients_term {u : ℕ → ℂ}
    (hu : BoundedCoefficients u) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n ↦ ‖partialCoefficients u n * z ^ n‖) :=
  summable_norm_partialCoefficients_term_of_summable
    (summable_norm_powerSeries_term hu hz) hz

/-- The generating function of prefix sums is the original generating function divided by
`1-z`, written without division. -/
theorem one_sub_mul_powerSeries_partialCoefficients_of_summable {u : ℕ → ℂ} {z : ℂ}
    (hU : Summable (fun n ↦ ‖u n * z ^ n‖)) (hz : ‖z‖ < 1) :
    (1 - z) * powerSeries (partialCoefficients u) z = powerSeries u z := by
  have hG : Summable (fun n : ℕ ↦ ‖z ^ n‖) :=
    summable_norm_geometric_of_norm_lt_one hz
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hU hG
  have hprefix :
      powerSeries u z * (∑' n : ℕ, z ^ n) = powerSeries (partialCoefficients u) z := by
    rw [powerSeries, powerSeries]
    rw [hcauchy]
    apply tsum_congr
    intro n
    rw [partialCoefficients, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    calc
      u k * z ^ k * z ^ (n - k) = u k * (z ^ k * z ^ (n - k)) := by ring
      _ = u k * z ^ n := by rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [← hprefix]
  calc
    (1 - z) * (powerSeries u z * ∑' n : ℕ, z ^ n) =
        powerSeries u z * ((1 - z) * ∑' n : ℕ, z ^ n) := by ring
    _ = powerSeries u z := by
      rw [(summable_geometric_of_norm_lt_one hz).one_sub_mul_tsum_pow]
      simp

/-- Bounded-coefficient specialization of the prefix generating-function identity. -/
theorem one_sub_mul_powerSeries_partialCoefficients {u : ℕ → ℂ}
    (hu : BoundedCoefficients u) {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z) * powerSeries (partialCoefficients u) z = powerSeries u z :=
  one_sub_mul_powerSeries_partialCoefficients_of_summable
    (summable_norm_powerSeries_term hu hz) hz

/-! ### Coefficients attached to a set of natural numbers -/

/-- The complex-valued indicator coefficients of a set of natural numbers. -/
noncomputable def indicatorCoefficient (A : Set ℕ) (n : ℕ) : ℂ :=
  by
    classical
    exact if n ∈ A then 1 else 0

theorem boundedCoefficients_indicator (A : Set ℕ) :
    BoundedCoefficients (indicatorCoefficient A) := by
  classical
  refine ⟨1, fun n ↦ ?_⟩
  simp only [indicatorCoefficient]
  split <;> simp

/-- The convolution of the indicator sequence counts ordered representations. -/
theorem indicator_antidiagonal_eq_representation (A : Set ℕ) (n : ℕ) :
    (∑ kl ∈ antidiagonal n,
      indicatorCoefficient A kl.1 * indicatorCoefficient A kl.2) =
      (representation A n : ℂ) := by
  classical
  rw [show (∑ kl ∈ antidiagonal n,
      indicatorCoefficient A kl.1 * indicatorCoefficient A kl.2) =
      ∑ k ∈ Finset.range (n + 1),
        indicatorCoefficient A k * indicatorCoefficient A (n - k) by
    simpa using Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ indicatorCoefficient A i * indicatorCoefficient A j) n]
  rw [representation]
  simp only [indicatorCoefficient, ite_mul, one_mul, zero_mul, ← ite_and]
  rw [Finset.sum_boole]

/-- Squaring the set generating function produces the ordered representation coefficients. -/
theorem powerSeries_indicator_sq (A : Set ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    powerSeries (indicatorCoefficient A) z ^ 2 =
      ∑' n : ℕ, (representation A n : ℂ) * z ^ n := by
  rw [pow_two, powerSeries_mul (boundedCoefficients_indicator A)
    (boundedCoefficients_indicator A) hz]
  apply tsum_congr
  intro n
  rw [indicator_antidiagonal_eq_representation]

theorem representation_le_succ (A : Set ℕ) (n : ℕ) :
    representation A n ≤ n + 1 := by
  classical
  rw [representation]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)

/-- The representation series is absolutely convergent in the open unit disc. -/
theorem summable_norm_representation_term (A : Set ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n ↦ ‖(representation A n : ℂ) * z ^ n‖) := by
  have hr : ‖(‖z‖ : ℝ)‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)] using hz
  have hn : Summable (fun n : ℕ ↦ (n : ℝ) * ‖z‖ ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr)
  have hg : Summable (fun n : ℕ ↦ ‖z‖ ^ n) :=
    summable_geometric_of_norm_lt_one hr
  have hmajor : Summable (fun n : ℕ ↦ ((n : ℝ) + 1) * ‖z‖ ^ n) := by
    simpa [add_mul] using hn.add hg
  refine hmajor.of_norm_bounded fun n ↦ ?_
  rw [norm_norm, norm_mul, norm_natCast, norm_pow]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast representation_le_succ A n)
    (pow_nonneg (norm_nonneg z) n)

/-- Prefix sums of representation numbers are the complex casts of `cumulative`. -/
theorem partialCoefficients_representation (A : Set ℕ) (N : ℕ) :
    partialCoefficients (fun n ↦ (representation A n : ℂ)) N = (cumulative A N : ℂ) := by
  simp [partialCoefficients, cumulative]

/-- The exact generating-function identity for cumulative representation counts. -/
theorem one_sub_mul_cumulative_series (A : Set ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z) * (∑' N : ℕ, (cumulative A N : ℂ) * z ^ N) =
      ∑' n : ℕ, (representation A n : ℂ) * z ^ n := by
  have h := one_sub_mul_powerSeries_partialCoefficients_of_summable
    (summable_norm_representation_term A hz) hz
  rw [powerSeries, powerSeries] at h
  simpa only [partialCoefficients_representation] using h

/-- The bounded discrepancy, viewed as a complex coefficient sequence. -/
noncomputable def cumulativeError (A : Set ℕ) (c : ℝ) (N : ℕ) : ℂ :=
  ((cumulative A N : ℝ) - c * (N : ℝ) : ℝ)

theorem boundedCoefficients_cumulativeError {A : Set ℕ} {c C : ℝ}
    (h : ∀ N : ℕ, |(cumulative A N : ℝ) - c * (N : ℝ)| ≤ C) :
    BoundedCoefficients (cumulativeError A c) := by
  refine ⟨C, fun N ↦ ?_⟩
  rw [cumulativeError, Complex.norm_real, Real.norm_eq_abs]
  exact h N

/-- The analytic identity supplied by a bounded cumulative error.  The factor `z` in the main
term reflects the convention `∑_{n ≤ N} r(n) = c N + E(N)` with the sum starting at `N = 0`. -/
theorem representation_series_eq_main_add_error {A : Set ℕ} {c C : ℝ}
    (h : ∀ N : ℕ, |(cumulative A N : ℝ) - c * (N : ℝ)| ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' n : ℕ, (representation A n : ℂ) * z ^ n) =
      (c : ℂ) * z / (1 - z) + (1 - z) * powerSeries (cumulativeError A c) z := by
  have hne : 1 - z ≠ 0 := by
    intro hzero
    have hz1 : z = 1 := (sub_eq_zero.mp hzero).symm
    rw [hz1] at hz
    rw [norm_one] at hz
    exact (lt_irrefl 1) hz
  have hmain : Summable (fun N : ℕ ↦ (c : ℂ) * (N : ℂ) * z ^ N) :=
    by simpa [mul_assoc] using
      (hasSum_coe_mul_geometric_of_norm_lt_one hz).summable.mul_left (c : ℂ)
  have herr : Summable (fun N : ℕ ↦ cumulativeError A c N * z ^ N) :=
    summable_powerSeries_term (boundedCoefficients_cumulativeError h) hz
  rw [← one_sub_mul_cumulative_series A hz]
  have hsplit :
      (∑' N : ℕ, (cumulative A N : ℂ) * z ^ N) =
      (∑' N : ℕ, (c : ℂ) * (N : ℂ) * z ^ N) +
          ∑' N : ℕ, cumulativeError A c N * z ^ N := by
    rw [← hmain.tsum_add herr]
    apply tsum_congr
    intro N
    rw [← add_mul]
    congr 1
    simp [cumulativeError]
  have hmain_tsum :
      (∑' N : ℕ, (c : ℂ) * (N : ℂ) * z ^ N) =
        (c : ℂ) * (z / (1 - z) ^ 2) := by
    calc
      (∑' N : ℕ, (c : ℂ) * (N : ℂ) * z ^ N) =
          ∑' N : ℕ, (c : ℂ) * ((N : ℂ) * z ^ N) := by
            apply tsum_congr
            intro N
            ring
      _ = (c : ℂ) * ∑' N : ℕ, (N : ℂ) * z ^ N := tsum_mul_left
      _ = (c : ℂ) * (z / (1 - z) ^ 2) := by
        rw [tsum_coe_mul_geometric_of_norm_lt_one hz]
  rw [hsplit, powerSeries]
  rw [hmain_tsum]
  field_simp [hne]

/-- The squared indicator generating function in the form used by the bounded-error argument. -/
theorem powerSeries_indicator_sq_eq_main_add_error {A : Set ℕ} {c C : ℝ}
    (h : ∀ N : ℕ, |(cumulative A N : ℝ) - c * (N : ℝ)| ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) :
    powerSeries (indicatorCoefficient A) z ^ 2 =
      (c : ℂ) * z / (1 - z) + (1 - z) * powerSeries (cumulativeError A c) z := by
  rw [powerSeries_indicator_sq A hz]
  exact representation_series_eq_main_add_error h hz

end JSP000625
