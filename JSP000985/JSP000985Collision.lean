import Mathlib

/-!
# Glibichuk's collision lemma

This is Lemma 3 on p. 388 of A. A. Glibichuk, *Combinatorial
properties of sets of residues modulo a prime and the Erdős–Graham problem*,
Mat. Zametki 79 (2006), 384–395.  We state the argument over an arbitrary
field, since the proof uses only field cancellation.
-/

namespace JSP000985

section Collision

variable {F : Type*} [Field F]

/-- The set `A + ξ B`, represented by its defining image. -/
noncomputable def scaledSumset {K : Type*} [Semiring K]
    (ξ : K) (A B : Finset K) : Finset K := by
  classical
  exact (A ×ˢ B).image fun x ↦ x.1 + ξ * x.2

@[simp] theorem mem_scaledSumset {K : Type*} [Semiring K]
    (ξ x : K) (A B : Finset K) :
    x ∈ scaledSumset ξ A B ↔ ∃ a ∈ A, ∃ b ∈ B, a + ξ * b = x := by
  classical
  simp only [scaledSumset, Finset.mem_image, Finset.mem_product, Prod.exists]
  aesop

/-- Glibichuk's set `I(A,B)` from Lemma 3. -/
noncomputable def collisionSet (A B : Finset F) : Finset F := by
  classical
  exact ((((A ×ˢ A) ×ˢ A) ×ˢ ((B ×ˢ B) ×ˢ B)).image fun x ↦
    (x.2.1.1 - x.2.1.2) * x.1.1.1 + (x.1.1.2 - x.1.2) * x.2.2)

/-- If the map `(a,b) ↦ a + ξb` has a collision, multiplication by the
nonzero difference of the two `b` coordinates embeds `A + ξB` in `I(A,B)`.
This is Glibichuk's Lemma 3. -/
theorem card_scaledSumset_le_card_collisionSet (A B : Finset F) (ξ : F)
    (hcard : (scaledSumset ξ A B).card < A.card * B.card) :
    (scaledSumset ξ A B).card ≤ (collisionSet A B).card := by
  classical
  let f : F × F → F := fun x ↦ x.1 + ξ * x.2
  have hmaps : Set.MapsTo f ↑(A ×ˢ B) ↑(scaledSumset ξ A B) := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hlt : (scaledSumset ξ A B).card < (A ×ˢ B).card := by
    simpa using hcard
  obtain ⟨x, hx, y, hy, hxy, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  have hbx : x.2 ≠ y.2 := by
    intro hb
    have ha : x.1 = y.1 := by
      simpa [f, hb] using heq
    exact hxy (Prod.ext ha hb)
  have hfactor : (x.2 - y.2) * ξ = y.1 - x.1 := by
    dsimp [f] at heq
    calc
      (x.2 - y.2) * ξ = ξ * x.2 - ξ * y.2 := by ring
      _ = y.1 - x.1 := by linear_combination heq
  let g : F → F := fun z ↦ (x.2 - y.2) * z
  have hg_inj : Function.Injective g := by
    intro u v huv
    exact mul_left_cancel₀ (sub_ne_zero.mpr hbx) huv
  have hsubset : (scaledSumset ξ A B).image g ⊆ collisionSet A B := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨ab, hab, rfl⟩
    have hxa : x.1 ∈ A := (Finset.mem_product.mp hx).1
    have hxb : x.2 ∈ B := (Finset.mem_product.mp hx).2
    have hya : y.1 ∈ A := (Finset.mem_product.mp hy).1
    have hyb : y.2 ∈ B := (Finset.mem_product.mp hy).2
    have haa : ab.1 ∈ A := (Finset.mem_product.mp hab).1
    have hbb : ab.2 ∈ B := (Finset.mem_product.mp hab).2
    apply Finset.mem_image.mpr
    refine ⟨(((ab.1, y.1), x.1), ((x.2, y.2), ab.2)), ?_, ?_⟩
    · simp only [Finset.mem_product]
      exact ⟨⟨⟨haa, hya⟩, hxa⟩, ⟨⟨hxb, hyb⟩, hbb⟩⟩
    · dsimp [g]
      rw [mul_add, ← hfactor]
      ring
  calc
    (scaledSumset ξ A B).card = ((scaledSumset ξ A B).image g).card := by
      symm
      exact Finset.card_image_of_injective _ hg_inj
    _ ≤ (collisionSet A B).card := Finset.card_le_card hsubset

#print axioms card_scaledSumset_le_card_collisionSet

end Collision

end JSP000985
