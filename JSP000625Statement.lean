import Mathlib

/-! JSP-000625 (Erdős problem 763): ordered two-term representations. -/
namespace JSP000625

/-- Counts ordered pairs `(a,b) ∈ A × A` with `a + b = n`.
The second coordinate is uniquely `n-a`; the range restriction prevents truncation artifacts. -/
noncomputable def representation (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter fun a => a ∈ A ∧ n - a ∈ A).card

/-- Cumulative ordered representation count, including `n=0` and `n=N`. -/
noncomputable def cumulative (A : Set ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), representation A n

end JSP000625
