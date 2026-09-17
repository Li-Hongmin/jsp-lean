import Mathlib

/-!
# JSP-000985: the exact scoped Erdős–Graham statement

The bound counts summands with repetition; zero summands are allowed.
Only integers with a genuine multiplicative inverse modulo `p` are admissible.
-/
namespace JSP000985

/-- `a` is a sum of at most `C` reciprocals from the initial interval ending at `p^ε`.
The nonzero condition removes multiples of `p` when `ε ≥ 1`. -/
def Representable (p : ℕ) (ε : ℝ) (C : ℕ) (a : ZMod p) : Prop :=
  ∃ (k : ℕ) (n : Fin k → ℕ), k ≤ C ∧
    (∀ i, 1 ≤ n i ∧ (n i : ℝ) ≤ (p : ℝ) ^ ε ∧ (n i : ZMod p) ≠ 0) ∧
    ∑ i, (n i : ZMod p)⁻¹ = a

/-- The catalog's scoped assertion. In particular `C` is independent of `p` and `a`. -/
def CatalogStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℕ,
    ∀ p : ℕ, p.Prime → ∀ a : ZMod p, Representable p ε C a

end JSP000985
