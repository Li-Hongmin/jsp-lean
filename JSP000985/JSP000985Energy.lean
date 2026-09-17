import JSP000985Collision

/-!
# Glibichuk's collision count (Lemma 1, pp. 386–387)

Source: A. A. Glibichuk, Mat. Zametki 79 (2006), 384–395,
DOI 10.4213/mzm2708. The proof counts each off-diagonal collision
for at most one slope and each diagonal collision for every slope.
-/
namespace JSP000985
open Finset
open scoped Classical

/-- The number of ordered collisions of the affine map `(a,b) ↦ a + ξ*b`. -/
noncomputable def collisionCount {F : Type*} [Field F]
    (A B : Finset F) (ξ : F) : ℕ := by
  exact (((A ×ˢ B) ×ˢ (A ×ˢ B)).filter
    (fun q ↦ q.1.1 + ξ * q.1.2 = q.2.1 + ξ * q.2.2)).card

/-- Two distinct pairs can collide for at most one slope. This is the
unique-slope observation in the proof of Glibichuk's Lemma 1. -/
theorem collision_slope_unique {F : Type*} [Field F]
    (x y : F × F) (hxy : x ≠ y) {ξ η : F}
    (hξ : x.1 + ξ * x.2 = y.1 + ξ * y.2)
    (hη : x.1 + η * x.2 = y.1 + η * y.2) : ξ = η := by
  have hb : x.2 ≠ y.2 := by
    intro h
    have ha : x.1 = y.1 := by simpa [h] using hξ
    exact hxy (Prod.ext ha h)
  have hz : (ξ - η) * (x.2 - y.2) = 0 := by linear_combination hξ - hη
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hb))

/-- The double-counting inequality before (5) in Glibichuk's Lemma 1.
It even holds when the slope set contains zero. -/
theorem sum_collisionCount_le {F : Type*} [Field F]
    (A B C : Finset F) :
    ∑ ξ ∈ C, collisionCount A B ξ ≤
      A.card * B.card * C.card + (A.card * B.card) ^ 2 := by
  let X := A ×ˢ B
  have hswap : (∑ ξ ∈ C, collisionCount A B ξ) =
      ∑ q ∈ X ×ˢ X,
        (C.filter (fun ξ ↦ q.1.1 + ξ * q.1.2 = q.2.1 + ξ * q.2.2)).card := by
    simp only [collisionCount, card_eq_sum_ones, sum_filter]
    exact sum_comm
  rw [hswap]
  calc
    _ ≤ ∑ q ∈ X ×ˢ X, ((if q.1 = q.2 then C.card else 0) + 1) := by
      apply sum_le_sum
      intro q hq
      by_cases hq' : q.1 = q.2
      · simp [hq']
      · simp only [hq', ↓reduceIte, zero_add]
        apply card_le_one.mpr
        intro ξ hξ η hη
        exact collision_slope_unique q.1 q.2 hq'
          (mem_filter.mp hξ).2 (mem_filter.mp hη).2
    _ = X.card * C.card + X.card ^ 2 := by
      rw [sum_add_distrib]
      simp [sum_product, sq]
    _ = _ := by simp [X]

/-- Fiberwise form of the collision count, as in Glibichuk's proof. -/
theorem collisionCount_eq_sum_sq {F : Type*} [Field F]
    (A B : Finset F) (ξ : F) :
    collisionCount A B ξ = ∑ z ∈ scaledSumset ξ A B,
      ((A ×ˢ B).filter (fun x ↦ x.1 + ξ * x.2 = z)).card ^ 2 := by
  unfold collisionCount
  simp_rw [sq, ← card_product]
  rw [← card_disjiUnion]
  swap
  · aesop (add simp [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left])
  · congr 1
    ext q
    simp only [mem_filter, mem_product, mem_disjiUnion]
    constructor
    · intro h
      refine ⟨q.1.1 + ξ * q.1.2, ?_, ⟨⟨h.1.1, rfl⟩, ⟨h.1.2, h.2.symm⟩⟩⟩
      exact mem_image.mpr ⟨q.1, mem_product.mpr h.1.1, rfl⟩
    · rintro ⟨z, hz, ⟨⟨h1, he1⟩, ⟨h2, he2⟩⟩⟩
      exact ⟨⟨h1, h2⟩, he1.trans he2.symm⟩

/-- Cauchy–Schwarz applied to the representation multiplicities. -/
theorem card_sq_le_scaledSumset_mul_collisionCount {F : Type*}
    [Field F] (A B : Finset F) (ξ : F) :
    (A.card * B.card) ^ 2 ≤ (scaledSumset ξ A B).card * collisionCount A B ξ := by
  rw [collisionCount_eq_sum_sq]
  have hsum : ∑ z ∈ scaledSumset ξ A B,
      ((A ×ˢ B).filter (fun x ↦ x.1 + ξ * x.2 = z)).card = A.card * B.card := by
    simpa [scaledSumset] using
      (card_eq_sum_card_image (fun x : F × F ↦ x.1 + ξ * x.2) (A ×ˢ B)).symm
  rw [← hsum]
  simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ) (scaledSumset ξ A B)
    (fun _ ↦ 1) (fun z ↦ ((A ×ˢ B).filter (fun x ↦ x.1 + ξ * x.2 = z)).card)

/-- The plus and minus energies agree by swapping the two `B` coordinates,
exactly equation (4) of Glibichuk's proof. -/
theorem collisionCount_neg {F : Type*} [Field F]
    (A B : Finset F) (ξ : F) : collisionCount A B (-ξ) = collisionCount A B ξ := by
  unfold collisionCount
  apply card_bij (fun q _ ↦ ((q.1.1, q.2.2), (q.2.1, q.1.2)))
  · intro q hq
    simp only [mem_filter, mem_product] at hq ⊢
    refine ⟨⟨⟨hq.1.1.1, hq.1.2.2⟩, ⟨hq.1.2.1, hq.1.1.2⟩⟩, ?_⟩
    linear_combination hq.2
  · intro q hq r hr h
    cases q; cases r
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨Prod.ext h.1.1 h.2.2, Prod.ext h.2.1 h.1.2⟩
  · intro q hq
    refine ⟨((q.1.1, q.2.2), (q.2.1, q.1.2)), ?_, rfl⟩
    simp only [mem_filter, mem_product] at hq ⊢
    refine ⟨⟨⟨hq.1.1.1, hq.1.2.2⟩, ⟨hq.1.2.1, hq.1.1.2⟩⟩, ?_⟩
    linear_combination hq.2

/-- Glibichuk's Lemma 1, with the two rational lower bounds expressed
without division. The denominator `|A||B|+|C|` is positive because `C` is
nonempty. -/
theorem exists_large_scaledSumsets {F : Type*} [Field F]
    (A B C : Finset F) (hC : C.Nonempty) :
    ∃ ξ ∈ C,
      A.card * B.card * C.card ≤ (scaledSumset ξ A B).card * (A.card * B.card + C.card) ∧
      A.card * B.card * C.card ≤ (scaledSumset (-ξ) A B).card * (A.card * B.card + C.card) := by
  let N := A.card * B.card
  have havg : ∃ ξ ∈ C, collisionCount A B ξ * C.card ≤ N * C.card + N ^ 2 := by
    have hle : (∑ ξ ∈ C, collisionCount A B ξ * C.card) ≤
        ∑ _ξ ∈ C, (N * C.card + N ^ 2) := by
      simpa only [sum_mul, sum_const, smul_eq_mul, mul_comm C.card] using
        Nat.mul_le_mul_right C.card (sum_collisionCount_le A B C)
    exact exists_le_of_sum_le hC hle
  obtain ⟨ξ, hξ, havg⟩ := havg
  refine ⟨ξ, hξ, ?_, ?_⟩
  all_goals
    have hcs := card_sq_le_scaledSumset_mul_collisionCount A B ξ
    have hcsneg := card_sq_le_scaledSumset_mul_collisionCount A B (-ξ)
    rw [collisionCount_neg] at hcsneg
    change N * C.card ≤ _ * (N + C.card)
    change N ^ 2 ≤ _ at hcs hcsneg
    by_cases hN : N = 0
    · simp [hN]
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      apply (mul_le_mul_iff_right₀ hNpos).mp
      nlinarith [Nat.mul_le_mul_right C.card hcs,
        Nat.mul_le_mul_left (scaledSumset ξ A B).card havg,
        Nat.mul_le_mul_right C.card hcsneg,
        Nat.mul_le_mul_left (scaledSumset (-ξ) A B).card havg]

/-- Glibichuk's Lemma 2 (the paper works with odd primes).
The strict half-field bounds are written as integer inequalities. -/
theorem exists_half_scaledSumsets (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (A B : Finset (ZMod p)) (hAB : p < A.card * B.card) :
    ∃ ξ : ZMod p, ξ ≠ 0 ∧
      p < 2 * (scaledSumset ξ A B).card ∧
      p < 2 * (scaledSumset (-ξ) A B).card := by
  letI : Fact p.Prime := ⟨hp⟩
  let C : Finset (ZMod p) := univ.erase 0
  have hC : C.Nonempty := ⟨1, by simp [C]⟩
  have hCcard : C.card = p - 1 := by simp [C, ZMod.card]
  obtain ⟨ξ, hξ, hplus, hminus⟩ := exists_large_scaledSumsets A B C hC
  have hξ0 : ξ ≠ 0 := (mem_erase.mp hξ).1
  rw [hCcard] at hplus hminus
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have hpge := hp.two_le
  have hmpos : 0 < m := by omega
  have hsub : p - 1 = 2 * m := by omega
  rw [hsub] at hplus hminus
  have half_bound : ∀ t : ℕ,
      A.card * B.card * (2 * m) ≤ t * (A.card * B.card + 2 * m) → p < 2 * t := by
    intro t ht
    by_contra h
    have htm : t ≤ m := by omega
    have hmul := Nat.mul_le_mul_right (A.card * B.card + 2 * m) htm
    nlinarith
  exact ⟨ξ, hξ0, half_bound _ hplus, half_bound _ hminus⟩

#print axioms collision_slope_unique
#print axioms sum_collisionCount_le
#print axioms collisionCount_eq_sum_sq
#print axioms card_sq_le_scaledSumset_mul_collisionCount
#print axioms collisionCount_neg
#print axioms exists_large_scaledSumsets
#print axioms exists_half_scaledSumsets
end JSP000985
