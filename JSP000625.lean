import JSP000625Assembly

/-!
JSP-000625 / Erdős problem 763: the bounded-error Erdős--Fuchs theorem.
The finite-window proof follows Newman, Analytic Number Theory (1998),
Chapter III, pp. 35--38, specialized to bounded discrepancy.
-/

open Filter Topology
namespace JSP000625

/-- No set of natural numbers has cumulative ordered two-term representation
counts equal to a positive linear function with uniformly bounded error. -/
theorem erdos_fuchs_bounded_error :
    ∀ A : Set ℕ, ∀ c : ℝ, 0 < c →
      ¬ ∃ C : ℝ, ∀ N : ℕ, |(cumulative A N : ℝ) - c * (N : ℝ)| ≤ C := by
  intro A c hc ⟨C, h⟩
  have hC : 0 ≤ C := (abs_nonneg _).trans (h 0)
  apply contradiction_of_newman_estimate hc hC h
  intro m
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with r hr1 hr
  exact normalized_newman_estimate hc hC h m hr.le hr1

#print axioms erdos_fuchs_bounded_error
end JSP000625
