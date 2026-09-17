import JSP000985Statement

/-!
# Finite-prime bookkeeping for JSP-000985

These elementary lemmas isolate the formal passage from a bound valid for all
sufficiently large primes to a bound valid for every prime.  They do not prove
the uniform estimate required by the catalog statement.
-/

namespace JSP000985

/-- Increasing the allowed number of summands preserves representability. -/
theorem Representable.mono {p : ℕ} {ε : ℝ} {C D : ℕ} {a : ZMod p}
    (hCD : C ≤ D) (ha : Representable p ε C a) : Representable p ε D a := by
  rcases ha with ⟨k, n, hk, hn, hs⟩
  exact ⟨k, n, hk.trans hCD, hn, hs⟩

/-- For a prime modulus, every residue is the sum of `a.val` copies of `1⁻¹`.
This gives the elementary modulus-dependent bound `p - 1`. -/
theorem representable_sub_one (p : ℕ) (hp : p.Prime) (ε : ℝ) (hε : 0 < ε)
    (a : ZMod p) : Representable p ε (p - 1) a := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨a.val, fun _ ↦ 1, Nat.le_sub_one_of_lt a.val_lt, ?_, ?_⟩
  · intro i
    refine ⟨le_rfl, ?_, ?_⟩
    simpa using Real.one_le_rpow (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_le) hε.le
    simpa using (one_ne_zero : (1 : ZMod p) ≠ 0)
  · simpa using ZMod.natCast_zmod_val a

/-- A uniform bound for primes at least `P` extends to all primes after replacing
the bound by `max C P`; the finitely many smaller primes use `p - 1` copies of
`1`. -/
theorem uniform_of_large_primes (ε : ℝ) (hε : 0 < ε) (P C : ℕ)
    (hlarge : ∀ p : ℕ, p.Prime → P ≤ p →
      ∀ a : ZMod p, Representable p ε C a) :
    ∀ p : ℕ, p.Prime → ∀ a : ZMod p, Representable p ε (max C P) a := by
  intro p hp a
  by_cases hP : P ≤ p
  · exact (hlarge p hp hP a).mono (Nat.le_max_left C P)
  · apply (representable_sub_one p hp ε hε a).mono
    exact le_trans (Nat.sub_le p 1) (le_trans (Nat.le_of_lt (Nat.lt_of_not_ge hP))
      (Nat.le_max_right C P))

#print axioms Representable.mono
#print axioms representable_sub_one
#print axioms uniform_of_large_primes

end JSP000985
