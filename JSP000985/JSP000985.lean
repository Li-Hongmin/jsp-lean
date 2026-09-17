import JSP000985Algebra
import JSP000985Covering

/-!
# JSP-000985: a partial formalization with an explicit remaining hypothesis

`catalog_of_reciprocalGrowth` is conditional. `ReciprocalGrowth` is NOT
proved here. Its published proof is the prime-denominator construction in
Glibichuk's Lemma 4, pp. 391–393. Thus this file does not claim the catalog
statement unconditionally.
-/
namespace JSP000985
open Finset
open scoped Pointwise

/-- The exact unproved input isolated from Glibichuk's Lemma 4:
for every positive exponent, sufficiently large primes have an
antisymmetric set of more than `sqrt p` residues, each a sum of boundedly
many reciprocals from the interval with half that exponent. -/
def ReciprocalGrowth : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s P : ℕ,
    ∀ p : ℕ, p.Prime → P ≤ p → ∃ B : Finset (ZMod p),
      Disjoint B (-B) ∧ p < B.card * B.card ∧
      ∀ b ∈ B, Representable p (ε / 2) s b

/-- Membership in a pointwise sumset concatenates reciprocal representations. -/
theorem representable_mem_add {p : ℕ} {ε : ℝ} {C D : ℕ}
    (A B : Finset (ZMod p))
    (hA : ∀ a ∈ A, Representable p ε C a)
    (hB : ∀ b ∈ B, Representable p ε D b)
    (x : ZMod p) (hx : x ∈ A + B) : Representable p ε (C + D) x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hx
  exact (hA a ha).add (hB b hb)

/-- Four summands of elements already represented by `C` reciprocals need
at most `4*C` reciprocal summands. -/
theorem representable_mem_fourfold {p : ℕ} {ε : ℝ} {C : ℕ}
    (A : Finset (ZMod p)) (hA : ∀ a ∈ A, Representable p ε C a)
    (x : ZMod p) (hx : x ∈ fourfold A) : Representable p ε (4 * C) x := by
  have hAA := representable_mem_add A A hA hA
  have h := representable_mem_add (A + A) (A + A) hAA hAA x hx
  convert h using 1; ring

/-- The product expansion at the end of the proof of Glibichuk's Lemma 4,
followed by Theorem 1. This is unconditional once the indicated set `B`
is supplied. -/
theorem representable_of_large_antisymmetric (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (ε : ℝ) (s : ℕ) (B : Finset (ZMod p))
    (hB : Disjoint B (-B)) (hcard : p < B.card * B.card)
    (hrep : ∀ b ∈ B, Representable p (ε / 2) s b) :
    ∀ a : ZMod p, Representable p ε (8 * (s * s)) a := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hprod : ∀ x ∈ B * B, Representable p ε (s * s) x := by
    intro x hx
    obtain ⟨b, hb, c, hc, rfl⟩ := mem_mul.mp hx
    have h := (hrep b hb).mul hp (hrep c hc)
    convert h using 1; ring
  have hfour := representable_mem_fourfold (B * B) hprod
  intro a
  have ha : a ∈ fourfold (B * B) + fourfold (B * B) := by
    rw [eightfold_product_eq_univ p hp hp2 B B hB hcard]
    exact mem_univ a
  have h := representable_mem_add _ _ hfour hfour a ha
  convert h using 1; ring

/-- **Conditional reduction, not a proof of `CatalogStatement`.**
The finite-field covering theorem, product expansion, and finite-prime
bookkeeping reduce the catalog statement to the explicitly stated growth
input. No axiom or placeholder is used for that input. -/
theorem catalog_of_reciprocalGrowth (hgrowth : ReciprocalGrowth) : CatalogStatement := by
  intro ε hε
  obtain ⟨s, P, hlarge⟩ := hgrowth ε hε
  refine ⟨max (8 * (s * s)) (max P 3), ?_⟩
  apply uniform_of_large_primes ε hε (max P 3) (8 * (s * s))
  intro p hp hP
  obtain ⟨B, hB, hcard, hrep⟩ := hlarge p hp (le_trans (le_max_left _ _) hP)
  have hp2 : p ≠ 2 := by have := le_trans (le_max_right P 3) hP; omega
  exact representable_of_large_antisymmetric p hp hp2 ε s B hB hcard hrep

#print axioms representable_mem_add
#print axioms representable_mem_fourfold
#print axioms representable_of_large_antisymmetric
#print axioms catalog_of_reciprocalGrowth
end JSP000985
