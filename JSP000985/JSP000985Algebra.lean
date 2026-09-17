import JSP000985Finite

/-!
# Addition and multiplication of reciprocal representations

These are the bookkeeping operations in Glibichuk's proof of Lemma 4,
p. 393: multiply two sums over the shorter interval, then add eight such
products. The resulting denominators lie in the original interval.
-/
namespace JSP000985

/-- Concatenating two lists of admissible denominators adds their residues. -/
theorem Representable.add {p : ℕ} {ε : ℝ} {C D : ℕ} {a b : ZMod p}
    (ha : Representable p ε C a) (hb : Representable p ε D b) :
    Representable p ε (C + D) (a + b) := by
  obtain ⟨k, n, hk, hn, hs⟩ := ha
  obtain ⟨l, m, hl, hm, ht⟩ := hb
  refine ⟨k + l, Fin.addCases n m, Nat.add_le_add hk hl, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa only [Fin.addCases_left] using hn j
    · simpa only [Fin.addCases_right] using hm j
  · rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, hs, ht]

/-- Expanding a product of reciprocal sums multiplies denominator bounds,
so it adds the real exponents. -/
theorem Representable.mul {p : ℕ} (hp : p.Prime) {ε δ : ℝ} {C D : ℕ}
    {a b : ZMod p} (ha : Representable p ε C a) (hb : Representable p δ D b) :
    Representable p (ε + δ) (C * D) (a * b) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, n, hk, hn, hs⟩ := ha
  obtain ⟨l, m, hl, hm, ht⟩ := hb
  let e : Fin (k * l) ≃ Fin k × Fin l := finProdFinEquiv.symm
  refine ⟨k * l, (fun i ↦ n (e i).1 * m (e i).2), Nat.mul_le_mul hk hl, ?_, ?_⟩
  · intro i
    obtain ⟨hn1, hn2, hn3⟩ := hn (e i).1
    obtain ⟨hm1, hm2, hm3⟩ := hm (e i).2
    refine ⟨by nlinarith, ?_, ?_⟩
    · rw [Nat.cast_mul, Real.rpow_add (by exact_mod_cast hp.pos)]
      exact mul_le_mul hn2 hm2 (by positivity) (Real.rpow_nonneg (by positivity) _)
    · simpa only [Nat.cast_mul] using mul_ne_zero hn3 hm3
  · simp only [Nat.cast_mul, mul_inv]
    rw [e.sum_comp (fun ij ↦ (n ij.1 : ZMod p)⁻¹ * (m ij.2 : ZMod p)⁻¹)]
    rw [Fintype.sum_prod_type]
    dsimp only
    rw [← Finset.sum_mul_sum, hs, ht]

#print axioms Representable.add
#print axioms Representable.mul
end JSP000985
