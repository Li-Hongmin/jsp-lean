import JSP000985Energy

/-!
# Glibichuk's antisymmetric product-set covering theorem

This follows Theorem 1 on p. 388 of Glibichuk (2006): obtain both
half-field sumsets from Lemma 2, use antisymmetry to find a nonzero
scaling factor, embed the scaled set in `4AB`, and apply Cauchy–Davenport.
-/
namespace JSP000985
open Finset
open scoped Classical Pointwise

/-- Four summands, with repetition allowed. -/
def fourfold {F : Type*} [Add F] [DecidableEq F] (S : Finset F) : Finset F :=
  (S + S) + (S + S)

/-- The Cauchy–Davenport step used in Glibichuk's Theorems 1 and 2. -/
theorem add_self_eq_univ_of_half (p : ℕ) [NeZero p] (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : p < 2 * S.card) : S + S = univ := by
  have hne : S.Nonempty := card_pos.mp (by omega)
  have hcd := ZMod.cauchy_davenport hp hne hne
  have hmin : min p (S.card + S.card - 1) = p := min_eq_left (by omega)
  rw [hmin] at hcd
  apply eq_univ_of_card
  simpa only [ZMod.card] using le_antisymm (by simpa using card_le_univ (S + S)) hcd

/-- Glibichuk's Theorem 1 for odd primes: if `B` is antisymmetric and
`|A||B| > p`, every residue is a sum of eight products from `AB`. -/
theorem eightfold_product_eq_univ (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (A B : Finset (ZMod p)) (hB : Disjoint B (-B))
    (hAB : p < A.card * B.card) :
    fourfold (A * B) + fourfold (A * B) = univ := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ξ, hξ, hplus, hminus⟩ := exists_half_scaledSumsets p hp hp2 A B hAB
  have hcover := add_self_eq_univ_of_half p hp (scaledSumset ξ A B) hplus
  have hzero : (0 : ZMod p) ∈ scaledSumset ξ A B + scaledSumset ξ A B := by
    rw [hcover]
    exact mem_univ 0
  obtain ⟨u, hu, v, hv, huv⟩ := mem_add.mp hzero
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := (mem_scaledSumset ξ u A B).mp hu
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := (mem_scaledSumset ξ v A B).mp hv
  have hc : b₁ + b₂ ≠ 0 := by
    intro h
    have heq : b₁ = -b₂ := eq_neg_of_add_eq_zero_left h
    apply disjoint_left.mp hB hb₁
    rw [heq]
    simpa using hb₂
  have hfactor : (b₁ + b₂) * ξ = -(a₁ + a₂) := by
    linear_combination huv
  let T := (scaledSumset (-ξ) A B).image (fun x ↦ (b₁ + b₂) * x)
  have hTcard : T.card = (scaledSumset (-ξ) A B).card :=
    card_image_of_injective _ (mul_right_injective₀ hc)
  have hTsub : T ⊆ fourfold (A * B) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    obtain ⟨a₃, ha₃, b₃, hb₃, rfl⟩ := (mem_scaledSumset (-ξ) w A B).mp hw
    have hab (a b : ZMod p) (ha : a ∈ A) (hb : b ∈ B) : a * b ∈ A * B :=
      mem_mul.mpr ⟨a, ha, b, hb, rfl⟩
    apply mem_add.mpr
    refine ⟨a₃ * b₁ + a₃ * b₂,
      mem_add.mpr ⟨_, hab _ _ ha₃ hb₁, _, hab _ _ ha₃ hb₂, rfl⟩,
      a₁ * b₃ + a₂ * b₃,
      mem_add.mpr ⟨_, hab _ _ ha₁ hb₃, _, hab _ _ ha₂ hb₃, rfl⟩, ?_⟩
    linear_combination b₃ * hfactor
  have hfour : p < 2 * (fourfold (A * B)).card := by
    have hle := card_le_card hTsub
    rw [hTcard] at hle
    omega
  exact add_self_eq_univ_of_half p hp _ hfour

#print axioms add_self_eq_univ_of_half
#print axioms eightfold_product_eq_univ
end JSP000985
