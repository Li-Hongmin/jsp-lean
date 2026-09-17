import JSP000625Statement

/-!
Elementary finite counting identities for JSP-000625.
-/

namespace JSP000625

open Finset

/-- Ordered pairs from `A` on the natural-number antidiagonal of `n`. -/
noncomputable def representationPairs (A : Set ℕ) (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.HasAntidiagonal.antidiagonal n).filter fun p => p.1 ∈ A ∧ p.2 ∈ A

/-- The `0`-`1` coefficient of the characteristic series of `A`. -/
noncomputable def membershipCoeff (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact if n ∈ A then 1 else 0

/-- The defining one-coordinate count is the cardinality of the corresponding
filtered natural-number antidiagonal. -/
theorem representation_eq_card_antidiagonal_filter (A : Set ℕ) (n : ℕ) :
    representation A n = (representationPairs A n).card := by
  classical
  rw [representation, representationPairs, Finset.Nat.antidiagonal_eq_map]
  rw [Finset.filter_map]
  simp

/-- `representation` is the convolution of the two `0`-`1` characteristic
coefficient sequences, written as a sum over the natural antidiagonal. -/
theorem representation_eq_sum_antidiagonal (A : Set ℕ) (n : ℕ) :
    representation A n =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        membershipCoeff A p.1 * membershipCoeff A p.2 := by
  classical
  rw [representation, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  apply Finset.sum_congr (by simp [Nat.succ_eq_add_one])
  intro a ha
  by_cases h₁ : a ∈ A <;> by_cases h₂ : n - a ∈ A <;>
    simp [membershipCoeff, h₁, h₂]

/-- The elements of `A` that can occur in a pair whose sum is at most `N`. -/
noncomputable def elementsUpTo (A : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (N + 1)).filter fun a => a ∈ A

/-- The fiber with fixed sum `n` inside the finite square cut off at `N`. -/
noncomputable def pairFiber (A : Set ℕ) (N n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((elementsUpTo A N).product (elementsUpTo A N)).filter fun p =>
    p.1 + p.2 = n

/-- Ordered pairs from `A × A` whose sum is at most `N`. -/
noncomputable def cumulativePairs (A : Set ℕ) (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((elementsUpTo A N).product (elementsUpTo A N)).filter fun p =>
    p.1 + p.2 ≤ N

/-- Below the ambient cutoff, the fiber in the finite square is exactly the
filtered antidiagonal. -/
theorem pairFiber_eq_representationPairs (A : Set ℕ) {N n : ℕ} (hn : n ≤ N) :
    pairFiber A N n = representationPairs A n := by
  classical
  ext p
  simp [pairFiber, elementsUpTo, representationPairs]
  constructor
  · rintro ⟨⟨⟨hp₁N, hp₁A⟩, hp₂N, hp₂A⟩, hsum⟩
    exact ⟨hsum, hp₁A, hp₂A⟩
  · rintro ⟨hsum, hp₁A, hp₂A⟩
    exact ⟨⟨⟨by omega, hp₁A⟩, by omega, hp₂A⟩, hsum⟩

/-- The cumulative representation sum is exactly the number of ordered pairs
`(a,b) ∈ A × A` satisfying `a + b ≤ N`. -/
theorem cumulative_eq_card_pairs (A : Set ℕ) (N : ℕ) :
    cumulative A N = (cumulativePairs A N).card := by
  classical
  rw [cumulative]
  calc
    (∑ n ∈ Finset.range (N + 1), representation A n) =
        ∑ n ∈ Finset.range (N + 1), (pairFiber A N n).card := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [representation_eq_card_antidiagonal_filter,
        pairFiber_eq_representationPairs A (by simpa using hn)]
    _ = (((elementsUpTo A N).product (elementsUpTo A N)).filter fun p =>
          p.1 + p.2 ∈ Finset.range (N + 1)).card := by
      simpa [pairFiber] using
        (Finset.sum_card_fiberwise_eq_card_filter
          ((elementsUpTo A N).product (elementsUpTo A N))
          (Finset.range (N + 1)) (fun p : ℕ × ℕ => p.1 + p.2))
    _ = (cumulativePairs A N).card := by
      congr 1
      ext p
      simp [cumulativePairs]

/-- Trivial square bound for the number of pairs with bounded sum. -/
theorem cumulative_le_elementsUpTo_sq (A : Set ℕ) (N : ℕ) :
    cumulative A N ≤ (elementsUpTo A N).card ^ 2 := by
  rw [cumulative_eq_card_pairs, pow_two]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_product _ _)

/-- A finite ambient set uniformly bounds the size of every finite cutoff. -/
theorem elementsUpTo_card_le_ncard {A : Set ℕ} (hA : A.Finite) (N : ℕ) :
    (elementsUpTo A N).card ≤ A.ncard := by
  rw [Set.ncard_eq_toFinset_card A hA]
  apply Finset.card_le_card
  intro a ha
  have ha' : a ≤ N ∧ a ∈ A := by simpa [elementsUpTo] using ha
  exact hA.mem_toFinset.mpr ha'.2

/-- For finite `A`, all cumulative representation counts are bounded by
`|A|²`. -/
theorem cumulative_le_ncard_sq {A : Set ℕ} (hA : A.Finite) (N : ℕ) :
    cumulative A N ≤ A.ncard ^ 2 := by
  exact (cumulative_le_elementsUpTo_sq A N).trans
    (Nat.pow_le_pow_left (elementsUpTo_card_le_ncard hA N) 2)

/-- A positive linear main term with uniformly bounded real error forces the
underlying set to be infinite.  This is the elementary finite-set exclusion
used before the analytic part of Erdős--Fuchs. -/
theorem bounded_error_implies_infinite (A : Set ℕ) {c C : ℝ} (hc : 0 < c)
    (hbound : ∀ N : ℕ, |(cumulative A N : ℝ) - c * (N : ℝ)| ≤ C) :
    A.Infinite := by
  by_contra hAinf
  have hA : A.Finite := Set.not_infinite.mp hAinf
  obtain ⟨N, hN⟩ :=
    (exists_nat_gt ((C + (A.ncard ^ 2 : ℕ)) / c) :
      ∃ N : ℕ, (C + (A.ncard ^ 2 : ℕ)) / c < (N : ℝ))
  have hlarge : C + (A.ncard ^ 2 : ℕ) < c * (N : ℝ) := by
    have := (div_lt_iff₀ hc).mp hN
    simpa [mul_comm] using this
  have herr := hbound N
  have herrlow : -C ≤ (cumulative A N : ℝ) - c * (N : ℝ) :=
    (abs_le.mp herr).1
  have hcum : (cumulative A N : ℝ) ≤ (A.ncard ^ 2 : ℕ) := by
    exact_mod_cast cumulative_le_ncard_sq hA N
  linarith

end JSP000625
