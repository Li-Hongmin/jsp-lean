import Mathlib

/-! JSP-000906 (Erdős #1089). Lean 4.32.0 / Mathlib v4.32.0. -/


/-! ## Definitions -/

/-! Definitions for JSP-000906 (Erdős #1089). -/
namespace JSP000906

noncomputable section
attribute [local instance] Classical.propDecidable
open Finset

/-- Positive distances determined by distinct members of a finite set. -/
def distinctDistances {E : Type*} [MetricSpace E] (P : Finset E) : Finset ℝ :=
  ((P ×ˢ P).filter (fun xy => xy.1 ≠ xy.2)).image (fun xy => dist xy.1 xy.2)

theorem mem_distinctDistances {E : Type*} [MetricSpace E] {P : Finset E} {r : ℝ} :
    r ∈ distinctDistances P ↔ ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ dist x y = r := by
  classical
  simp only [distinctDistances, mem_image, mem_filter, mem_product, Prod.exists]
  aesop

theorem zero_not_mem_distinctDistances {E : Type*} [MetricSpace E] (P : Finset E) :
    0 ∉ distinctDistances P := by
  simp [mem_distinctDistances]

theorem distinctDistances_mono {E : Type*} [MetricSpace E] {P Q : Finset E}
    (h : P ⊆ Q) : distinctDistances P ⊆ distinctDistances Q := by
  intro r hr
  obtain ⟨x, hx, y, hy, hxy, hr⟩ := mem_distinctDistances.mp hr
  exact mem_distinctDistances.mpr ⟨x, h hx, y, h hy, hxy, hr⟩

/-- Every set of exactly `N` points determines at least `n` distances. -/
def Forces (d n N : ℕ) : Prop :=
  ∀ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = N → n ≤ (distinctDistances P).card

/-- Existence is separated from the least-number definition, to expose its proof obligation. -/
def HasThreshold (d n : ℕ) : Prop := ∃ N, Forces d n N

/-- The least forcing cardinality, with an explicit fallback until existence is proved. -/
def g (d n : ℕ) : ℕ :=
  if h : HasThreshold d n then Nat.find h else 0

theorem g_spec {d n : ℕ} (h : HasThreshold d n) : Forces d n (g d n) := by
  simpa [g, h] using Nat.find_spec h

theorem g_le {d n N : ℕ} (h : Forces d n N) : g d n ≤ N := by
  have hex : HasThreshold d n := ⟨N, h⟩
  simpa [g, hex] using Nat.find_min' hex h

theorem forces_mono {d n N M : ℕ} (h : Forces d n N) (hNM : N ≤ M) :
    Forces d n M := by
  intro P hP
  obtain ⟨Q, hQP, hQ⟩ := exists_subset_card_eq (hP ▸ hNM)
  exact (h Q hQ).trans (card_le_card (distinctDistances_mono hQP))

theorem card_lt_g_of_few_distances {d n : ℕ} (h : HasThreshold d n)
    (P : Finset (EuclideanSpace ℝ (Fin d))) (hP : (distinctDistances P).card < n) :
    P.card < g d n := by
  by_contra! hn
  exact (not_le_of_gt hP) (forces_mono (g_spec h) hn P rfl)

#print axioms mem_distinctDistances
#print axioms g_spec
#print axioms g_le
#print axioms card_lt_g_of_few_distances
end
end JSP000906


/-! ## Indicators -/

open scoped BigOperators

namespace JSP906

noncomputable def indicatorPoint {m : ℕ} (S : Finset (Fin m)) :
    EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun i => if i ∈ S then 1 else 0)

@[simp] theorem indicatorPoint_apply {m : ℕ} (S : Finset (Fin m)) (i : Fin m) :
    indicatorPoint S i = if i ∈ S then 1 else 0 := rfl

theorem indicatorPoint_injective {m : ℕ} :
    Function.Injective (indicatorPoint (m := m)) := by
  intro S T h
  ext i
  have hi := congrArg (fun x : EuclideanSpace ℝ (Fin m) => x i) h
  simp only [indicatorPoint_apply] at hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

@[simp] theorem sum_indicatorPoint {m : ℕ} (S : Finset (Fin m)) :
    ∑ i, indicatorPoint S i = (S.card : ℝ) := by
  simp [indicatorPoint_apply]

theorem indicatorPoint_dist_sq {m : ℕ} (S T : Finset (Fin m))
    (hcard : S.card = T.card) :
    dist (indicatorPoint S) (indicatorPoint T) ^ 2 = 2 * ((S \ T).card : ℝ) := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  have hp : ∀ i : Fin m, ((indicatorPoint S - indicatorPoint T) i) ^ 2 =
      (if i ∈ S \ T then (1 : ℝ) else 0) + (if i ∈ T \ S then (1 : ℝ) else 0) := by
    intro i
    simp only [PiLp.sub_apply, indicatorPoint_apply, Finset.mem_sdiff]
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.card_sdiff_comm hcard]
  ring

noncomputable def indicatorSet (m k : ℕ) : Finset (EuclideanSpace ℝ (Fin m)) :=
  ((Finset.univ : Finset (Fin m)).powersetCard k).image indicatorPoint

@[simp] theorem card_indicatorSet (m k : ℕ) :
    (indicatorSet m k).card = Nat.choose m k := by
  rw [indicatorSet, Finset.card_image_of_injective _ indicatorPoint_injective]
  simp

theorem indicatorSet_sum {m k : ℕ} {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ indicatorSet m k) : ∑ i, x i = (k : ℝ) := by
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
  have hcard := (Finset.mem_powersetCard.mp hS).2
  simpa [hcard] using sum_indicatorPoint S

theorem indicatorSet_dist {m k : ℕ} {x y : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ indicatorSet m k) (hy : y ∈ indicatorSet m k) (hxy : x ≠ y) :
    dist x y ∈ (Finset.Icc 1 k).image (fun j : ℕ => Real.sqrt (2 * (j : ℝ))) := by
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hy
  have hScard := (Finset.mem_powersetCard.mp hS).2
  have hTcard := (Finset.mem_powersetCard.mp hT).2
  have hc : S.card = T.card := hScard.trans hTcard.symm
  have hpos : 0 < (S \ T).card := by
    by_contra hn
    have hz : S \ T = ∅ := Finset.card_eq_zero.mp (by omega)
    have hsub : S ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp hz
    have heq : S = T := Finset.eq_of_subset_of_card_le hsub (by omega)
    exact hxy (congrArg indicatorPoint heq)
  refine Finset.mem_image.mpr ⟨(S \ T).card, ?_, ?_⟩
  · exact Finset.mem_Icc.mpr ⟨hpos, (Finset.card_le_card Finset.sdiff_subset).trans_eq hScard⟩
  · rw [← indicatorPoint_dist_sq S T hc, Real.sqrt_sq (dist_nonneg)]

theorem exists_indicatorSet (d k : ℕ) :
    ∃ P : Finset (EuclideanSpace ℝ (Fin (d+1))),
      P.card = Nat.choose (d+1) k ∧
      (∀ x ∈ P, ∑ i, x i = (k : ℝ)) ∧
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y →
        dist x y ∈ (Finset.Icc 1 k).image (fun j : ℕ => Real.sqrt (2 * (j : ℝ)))) := by
  exact ⟨indicatorSet (d+1) k, card_indicatorSet _ _,
    fun _ hx => indicatorSet_sum hx, fun _ hx _ hy hxy => indicatorSet_dist hx hy hxy⟩

#print axioms exists_indicatorSet
end JSP906


/-! ## Hyperplane -/

open scoped InnerProductSpace

open Module

namespace JSP000906

noncomputable section

/-- The sum of the coordinates on `ℝ^(d+1)`, as a linear functional. -/
def coordinateSum (d : ℕ) :
    EuclideanSpace ℝ (Fin (d + 1)) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by
    simp only [PiLp.add_apply]
    exact Finset.sum_add_distrib
  map_smul' r x := by
    change (∑ i, r * x i) = r * ∑ i, x i
    exact (Finset.mul_sum Finset.univ (fun i => x i) r).symm

@[simp]
theorem coordinateSum_apply (d : ℕ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    coordinateSum d x = ∑ i, x i :=
  rfl

/-- A convenient point whose coordinate sum is `c`. -/
def constantSumBasepoint (d : ℕ) (c : ℝ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  EuclideanSpace.single 0 c

@[simp]
theorem coordinateSum_constantSumBasepoint (d : ℕ) (c : ℝ) :
    coordinateSum d (constantSumBasepoint d c) = c := by
  simp [constantSumBasepoint, coordinateSum]

theorem coordinateSum_ne_zero (d : ℕ) : coordinateSum d ≠ 0 := by
  intro h
  have h' := LinearMap.congr_fun h (constantSumBasepoint d 1)
  rw [coordinateSum_constantSumBasepoint] at h'
  simpa using h'

/-- The zero-coordinate-sum subspace of `ℝ^(d+1)` has dimension `d`. -/
theorem finrank_coordinateSum_ker (d : ℕ) :
    finrank ℝ (LinearMap.ker (coordinateSum d)) = d := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero (coordinateSum_ne_zero d)
  rw [finrank_euclideanSpace_fin] at h
  omega

/-- An arbitrary orthonormal-coordinate identification of the zero-sum subspace with `ℝ^d`. -/
def zeroSumLinearIsometryEquiv (d : ℕ) :
    LinearMap.ker (coordinateSum d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  ((stdOrthonormalBasis ℝ (LinearMap.ker (coordinateSum d))).reindex
      (finCongr (finrank_coordinateSum_ker d))).repr

/-- Translate the affine constant-sum hyperplane to the zero-sum subspace and identify it
isometrically with `ℝ^d`. -/
def constantSumEmbedding (d : ℕ) (c : ℝ) :
    {x : EuclideanSpace ℝ (Fin (d + 1)) // ∑ i, x i = c} →
      EuclideanSpace ℝ (Fin d) :=
  fun x => zeroSumLinearIsometryEquiv d
    ⟨x.1 - constantSumBasepoint d c, by
      rw [LinearMap.mem_ker, map_sub, coordinateSum_apply, x.2,
        coordinateSum_constantSumBasepoint, sub_self]⟩

/-- The affine hyperplane embedding preserves all pairwise distances. -/
theorem constantSumEmbedding_dist (d : ℕ) (c : ℝ)
    (x y : {x : EuclideanSpace ℝ (Fin (d + 1)) // ∑ i, x i = c}) :
    dist (constantSumEmbedding d c x) (constantSumEmbedding d c y) = dist x y := by
  unfold constantSumEmbedding
  rw [LinearIsometryEquiv.dist_map]
  change dist (x.1 - constantSumBasepoint d c) (y.1 - constantSumBasepoint d c) = dist x.1 y.1
  simp only [dist_eq_norm]
  congr 1
  abel

theorem constantSumEmbedding_injective (d : ℕ) (c : ℝ) :
    Function.Injective (constantSumEmbedding d c) := by
  intro x y h
  have hdist : dist x y = 0 := by
    rw [← constantSumEmbedding_dist d c x y, h, dist_self]
  exact dist_eq_zero.mp hdist

theorem constantSumEmbedding_surjective (d : ℕ) (c : ℝ) :
    Function.Surjective (constantSumEmbedding d c) := by
  intro z
  let k : LinearMap.ker (coordinateSum d) := (zeroSumLinearIsometryEquiv d).symm z
  let b := constantSumBasepoint d c
  have hsum : ∑ i, (k.1 + b) i = c := by
    rw [← coordinateSum_apply, map_add, k.2, coordinateSum_constantSumBasepoint, zero_add]
  refine ⟨⟨k.1 + b, hsum⟩, ?_⟩
  unfold constantSumEmbedding
  rw [← (zeroSumLinearIsometryEquiv d).apply_symm_apply z]
  congr 1
  ext
  simp [k, b]

/-- The affine constant-sum hyperplane is isometric to `ℝ^d`. -/
def constantSumIsometryEquiv (d : ℕ) (c : ℝ) :
    {x : EuclideanSpace ℝ (Fin (d + 1)) // ∑ i, x i = c} ≃ᵢ
      EuclideanSpace ℝ (Fin d) where
  toEquiv := Equiv.ofBijective (constantSumEmbedding d c)
    ⟨constantSumEmbedding_injective d c, constantSumEmbedding_surjective d c⟩
  isometry_toFun := Isometry.of_dist_eq (constantSumEmbedding_dist d c)

#print axioms finrank_coordinateSum_ker
#print axioms constantSumEmbedding_dist
#print axioms constantSumEmbedding_injective
#print axioms constantSumEmbedding_surjective
#print axioms constantSumIsometryEquiv

end

end JSP000906


/-! ## ExactDistances -/

namespace JSP906

open JSP000906

/-- Two equally sized subsets can differ in exactly `j` coordinates on each side. -/
theorem exists_subsets_sdiff_card (m k j : ℕ) (hm : 2*k ≤ m) (hj : j ≤ k) :
    ∃ S T : Finset (Fin m), S.card = k ∧ T.card = k ∧ (S \ T).card = j := by
  classical
  obtain ⟨S, hSsub, hS⟩ := Finset.exists_subset_card_eq
    (show k ≤ (Finset.univ : Finset (Fin m)).card by simp; omega)
  obtain ⟨C, hCS, hC⟩ := Finset.exists_subset_card_eq (show j ≤ S.card by omega)
  have hcpl : k ≤ ((Finset.univ : Finset (Fin m)) \ S).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp
    omega
  obtain ⟨D, hDsub, hD⟩ := Finset.exists_subset_card_eq (hj.trans hcpl)
  have hDS : Disjoint D S := by
    apply Finset.disjoint_left.mpr
    intro x hx hxS
    exact (Finset.mem_sdiff.mp (hDsub hx)).2 hxS
  refine ⟨S, (S \ C) ∪ D, hS, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint (hDS.symm.mono_left Finset.sdiff_subset),
      Finset.card_sdiff_of_subset hCS, hS, hC, hD]
    omega
  · have heq : S \ ((S \ C) ∪ D) = C := by
      ext x
      have hd : x ∈ D → x ∉ S := fun hx => Finset.disjoint_left.mp hDS hx
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hx
        tauto
      · intro hx
        have hxS := hCS hx
        tauto
    rw [heq, hC]

theorem indicatorSet_distances_eq (m k : ℕ) (hm : 2*k ≤ m) :
    distinctDistances (indicatorSet m k) =
      (Finset.Icc 1 k).image (fun j : ℕ => Real.sqrt (2 * (j : ℝ))) := by
  classical
  apply Finset.Subset.antisymm
  · intro r hr
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := mem_distinctDistances.mp hr
    exact indicatorSet_dist hx hy hxy
  · intro r hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hjpos, hjle⟩ := Finset.mem_Icc.mp hj
    obtain ⟨S, T, hS, hT, hST⟩ := exists_subsets_sdiff_card m k j hm hjle
    apply mem_distinctDistances.mpr
    refine ⟨indicatorPoint S, ?_, indicatorPoint T, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨S, Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, hS⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨T, Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, hT⟩, rfl⟩
    · intro heq
      have : S = T := indicatorPoint_injective heq
      simp [this] at hST
      omega
    · have heq := indicatorPoint_dist_sq S T (hS.trans hT.symm)
      rw [hST] at heq
      rw [← heq, Real.sqrt_sq dist_nonneg]

theorem indicatorSet_distances_card (m k : ℕ) (hm : 2*k ≤ m) :
    (distinctDistances (indicatorSet m k)).card = k := by
  classical
  rw [indicatorSet_distances_eq m k hm, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    have heq := congrArg (fun t : ℝ => t ^ 2) hab
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at heq
    have : (a : ℝ) = (b : ℝ) := by linarith
    exact_mod_cast this

#print axioms indicatorSet_distances_card
end JSP906


/-! ## Lower -/

namespace JSP000906
noncomputable section
open Finset

/-- The subset-indicator construction, transferred isometrically into `ℝ^d`. -/
theorem exists_few_distance_set (d k : ℕ) :
    ∃ Q : Finset (EuclideanSpace ℝ (Fin d)),
      Q.card = Nat.choose (d + 1) k ∧ (distinctDistances Q).card ≤ k := by
  classical
  obtain ⟨P, hcard, hsum, hdist⟩ := JSP906.exists_indicatorSet d k
  let f : P → EuclideanSpace ℝ (Fin d) := fun x =>
    constantSumEmbedding d (k : ℝ) ⟨x.1, hsum x.1 x.2⟩
  have hf : Function.Injective f := by
    intro x y h
    have heq := constantSumEmbedding_injective d (k : ℝ) h
    apply Subtype.ext
    exact congrArg (fun z : {x : EuclideanSpace ℝ (Fin (d+1)) // ∑ i, x i = (k : ℝ)} => z.1) heq
  refine ⟨P.attach.image f, ?_, ?_⟩
  · rw [card_image_of_injective _ hf, card_attach, hcard]
  · have hsub : distinctDistances (P.attach.image f) ⊆
        (Icc 1 k).image (fun j : ℕ => Real.sqrt (2 * (j : ℝ))) := by
      intro r hr
      obtain ⟨x, hx, y, hy, hxy, rfl⟩ := mem_distinctDistances.mp hr
      obtain ⟨x, _, rfl⟩ := mem_image.mp hx
      obtain ⟨y, _, rfl⟩ := mem_image.mp hy
      have hne : x.1 ≠ y.1 := by
        intro h
        exact hxy (congrArg f (Subtype.ext h))
      have hd : dist (f x) (f y) = dist x.1 y.1 :=
        constantSumEmbedding_dist d (k : ℝ) _ _
      rw [hd]
      exact hdist _ x.2 _ y.2 hne
    calc
      _ ≤ ((Icc 1 k).image (fun j : ℕ => Real.sqrt (2 * (j : ℝ)))).card := card_le_card hsub
      _ ≤ (Icc 1 k).card := card_image_le
      _ = k := by simp

/-- The sharp lower bound, with existence of the threshold made explicit. -/
theorem lower_bound_of_hasThreshold {d n : ℕ} (hn : 2 ≤ n) (h : HasThreshold d n) :
    Nat.choose (d + 1) (n - 1) + 1 ≤ g d n := by
  obtain ⟨P, hc, hd⟩ := exists_few_distance_set d (n - 1)
  have hl := card_lt_g_of_few_distances h P (lt_of_le_of_lt hd (by omega))
  omega

#print axioms exists_few_distance_set
#print axioms lower_bound_of_hasThreshold
end
end JSP000906


/-! ## BBSDimension -/

open scoped BigOperators

namespace JSP906

noncomputable def boundedSumEquivExactSum (d s : ℕ) :
    {f : Fin d → ℕ // ∑ i, f i ≤ s} ≃
      {f : Fin (d+1) → ℕ // ∑ i, f i = s} where
  toFun f := ⟨Fin.cons (s - ∑ i, f.val i) f.val, by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega⟩
  invFun f := ⟨fun i => f.val i.succ, by
    change (∑ i : Fin d, f.val i.succ) ≤ s
    have := f.property
    rw [Fin.sum_univ_succ] at this
    omega⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    simp
  right_inv f := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      have := f.property
      rw [Fin.sum_univ_succ] at this
      omega
    · simp

noncomputable def boundedExponentsEquivSym (d s : ℕ) :
    {f : Fin d →₀ ℕ // f.sum (fun _ e => e) ≤ s} ≃ Sym (Fin (d+1)) s :=
  ((Finsupp.equivFunOnFinite.subtypeEquiv (by
    intro f
    simp [Finsupp.sum_fintype])).trans (boundedSumEquivExactSum d s)).trans
    (Sym.equivNatSumOfFintype (Fin (d+1)) s).symm

theorem finrank_restrictTotalDegree (d s : ℕ) :
    Module.finrank ℝ (MvPolynomial.restrictTotalDegree (Fin d) ℝ s) =
      Nat.choose (d+s) s := by
  classical
  let e : ↥{f : Fin d →₀ ℕ | f.sum (fun _ e => e) ≤ s} ≃ Sym (Fin (d+1)) s :=
    boundedExponentsEquivSym d s
  letI : Fintype ↥{f : Fin d →₀ ℕ | f.sum (fun _ e => e) ≤ s} :=
    Fintype.ofEquiv (Sym (Fin (d+1)) s) e.symm
  unfold MvPolynomial.restrictTotalDegree
  rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport ℝ
    {f : Fin d →₀ ℕ | f.sum (fun _ e => e) ≤ s})]
  rw [Fintype.card_congr e, Sym.card_sym_eq_choose]
  simp [Nat.add_comm, Nat.add_left_comm]

#print axioms finrank_restrictTotalDegree
end JSP906


/-! ## BBS -/

/-!
# The Bannai–Bannai–Stanton bound by the polynomial duality argument

The distance kernel has total degree `2 * s`, not `s`. If a weight vector
annihilates evaluation of every polynomial of degree at most `s`, its double
sum against the kernel vanishes: each kernel monomial has degree at most `s`
on at least one of the two variable blocks. The kernel is diagonal on the
point set, with constant nonzero diagonal, so the sum of squares of the
weights is zero. Thus the degree-`s` evaluation functionals are independent.
-/

open scoped BigOperators
open MvPolynomial
namespace JSP906.BBS

lemma split_degree {σ τ : Type*} (m : (σ ⊕ τ) →₀ ℕ) :
    (m.comapDomain Sum.inl Sum.inl_injective.injOn).sum (fun _ e ↦ e) +
    (m.comapDomain Sum.inr Sum.inr_injective.injOn).sum (fun _ e ↦ e) =
    m.sum (fun _ e ↦ e) := by
  conv_rhs => rw [← m.comapDomain_sumElim_comapDomain]
  simpa only [Function.comp_def] using (Finsupp.sum_sumElim
    (m.comapDomain Sum.inl Sum.inl_injective.injOn)
    (m.comapDomain Sum.inr Sum.inr_injective.injOn) (fun (_ : σ ⊕ τ) (e : ℕ) ↦ e)).symm

lemma split_eval {σ τ : Type*} (m : (σ ⊕ τ) →₀ ℕ) (x : σ → ℝ) (y : τ → ℝ) :
    eval (Sum.elim x y) (monomial m (1 : ℝ)) =
    eval x (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (1 : ℝ)) *
    eval y (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) (1 : ℝ)) := by
  simp only [eval_monomial, one_mul]
  conv_lhs => rw [← m.comapDomain_sumElim_comapDomain]
  exact Finsupp.prod_sumElim _ _ _

lemma weighted_monomial_zero {σ ι : Type*} [Fintype ι]
    (x : ι → σ → ℝ) (w : ι → ℝ) (s : ℕ)
    (hw : ∀ p : MvPolynomial σ ℝ, p.totalDegree ≤ s →
      ∑ i, w i * eval (x i) p = 0)
    (m : (σ ⊕ σ) →₀ ℕ) (c : ℝ)
    (hm : m.sum (fun _ e ↦ e) ≤ 2 * s) :
    ∑ i, ∑ j, w i * w j * eval (Sum.elim (x i) (x j)) (monomial m c) = 0 := by
  classical
  let l := m.comapDomain Sum.inl Sum.inl_injective.injOn
  let r := m.comapDomain Sum.inr Sum.inr_injective.injOn
  have hd : l.sum (fun _ e ↦ e) ≤ s ∨ r.sum (fun _ e ↦ e) ≤ s := by
    have := split_degree m
    dsimp [l, r]
    omega
  have he (i j : ι) : eval (Sum.elim (x i) (x j)) (monomial m c) =
      c * (eval (x i) (monomial l 1) * eval (x j) (monomial r 1)) := by
    rw [← split_eval]
    simp [eval_monomial]
  simp_rw [he]
  have hf : (∑ i, ∑ j, w i * w j *
      (c * (eval (x i) (monomial l 1) * eval (x j) (monomial r 1)))) =
      c * (∑ i, w i * eval (x i) (monomial l 1)) *
      (∑ j, w j * eval (x j) (monomial r 1)) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hf]
  rcases hd with hl | hr
  · rw [hw _ ((totalDegree_monomial_le l (1 : ℝ)).trans hl)]
    ring
  · rw [hw _ ((totalDegree_monomial_le r (1 : ℝ)).trans hr)]
    ring

lemma weighted_polynomial_zero {σ ι : Type*} [Fintype ι]
    (x : ι → σ → ℝ) (w : ι → ℝ) (s : ℕ)
    (hw : ∀ p : MvPolynomial σ ℝ, p.totalDegree ≤ s →
      ∑ i, w i * eval (x i) p = 0)
    (p : MvPolynomial (σ ⊕ σ) ℝ) (hp : p.totalDegree ≤ 2 * s) :
    ∑ i, ∑ j, w i * w j * eval (Sum.elim (x i) (x j)) p = 0 := by
  classical
  conv_lhs => enter [2, i, 2, j, 2]; rw [p.as_sum]
  simp_rw [eval_sum, Finset.mul_sum]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun m hm ↦
    weighted_monomial_zero x w s hw m (coeff m p) ((le_totalDegree hm).trans hp)

noncomputable def sqDistPolynomial (d : ℕ) : MvPolynomial (Fin d ⊕ Fin d) ℝ :=
  ∑ k, (X (Sum.inl k) - X (Sum.inr k)) ^ 2

lemma sqDistPolynomial_degree (d : ℕ) : (sqDistPolynomial d).totalDegree ≤ 2 := by
  classical
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_pow _ _).trans
  have h := totalDegree_sub (X (Sum.inl i) : MvPolynomial (Fin d ⊕ Fin d) ℝ)
    (X (Sum.inr i))
  simp only [totalDegree_X, max_self] at h
  omega

lemma eval_sqDistPolynomial (d : ℕ) (x y : EuclideanSpace ℝ (Fin d)) :
    eval (Sum.elim x y) (sqDistPolynomial d) = dist x y ^ 2 := by
  classical
  simp [sqDistPolynomial, EuclideanSpace.dist_sq_eq, Real.dist_eq, sq_abs]

noncomputable def kernelPolynomial (d : ℕ) (D : Finset ℝ) :
    MvPolynomial (Fin d ⊕ Fin d) ℝ :=
  ∏ a ∈ D, (sqDistPolynomial d - C (a ^ 2))

lemma kernelPolynomial_degree (d : ℕ) (D : Finset ℝ) :
    (kernelPolynomial d D).totalDegree ≤ 2 * D.card := by
  classical
  apply (totalDegree_finsetProd D _).trans
  calc
    (∑ a ∈ D, (sqDistPolynomial d - C (a ^ 2)).totalDegree) ≤ ∑ _a ∈ D, 2 := by
      apply Finset.sum_le_sum
      intro a _
      exact (totalDegree_sub_C_le _ _).trans (sqDistPolynomial_degree d)
    _ = 2 * D.card := by simp [mul_comm]

lemma eval_kernelPolynomial (d : ℕ) (D : Finset ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    eval (Sum.elim x y) (kernelPolynomial d D) = ∏ a ∈ D, (dist x y ^ 2 - a ^ 2) := by
  classical
  simp [kernelPolynomial, eval_sqDistPolynomial]

lemma eval_kernelPolynomial_diag (d : ℕ) (D : Finset ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    eval (Sum.elim x x) (kernelPolynomial d D) = ∏ a ∈ D, -(a ^ 2) := by
  simp [eval_kernelPolynomial]

lemma eval_kernelPolynomial_offdiag (d : ℕ) (D : Finset ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) (h : dist x y ∈ D) :
    eval (Sum.elim x y) (kernelPolynomial d D) = 0 := by
  classical
  rw [eval_kernelPolynomial]
  exact Finset.prod_eq_zero h (sub_self _)

noncomputable def evaluation (d s : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    Module.Dual ℝ (restrictTotalDegree (Fin d) ℝ s) :=
  (aeval x).toLinearMap.comp (restrictTotalDegree (Fin d) ℝ s).subtype

@[simp] lemma evaluation_apply (d s : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (p : restrictTotalDegree (Fin d) ℝ s) :
    evaluation d s x p = eval x p.val := by
  rfl

lemma evaluations_linearIndependent (d : ℕ) (P : Finset (EuclideanSpace ℝ (Fin d)))
    (D : Finset ℝ) (hD : 0 ∉ D)
    (hP : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → dist x y ∈ D) :
    LinearIndependent ℝ (fun x : P ↦ evaluation d D.card x.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro w hw i
  have hann (p : MvPolynomial (Fin d) ℝ) (hp : p.totalDegree ≤ D.card) :
      ∑ j : P, w j * eval j.val p = 0 := by
    have h := congrArg (fun f : Module.Dual ℝ (restrictTotalDegree (Fin d) ℝ D.card) ↦
      f ⟨p, (mem_restrictTotalDegree _ _ _).mpr hp⟩) hw
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, evaluation_apply,
      smul_eq_mul, LinearMap.zero_apply] using h
  have hz := weighted_polynomial_zero (fun j : P ↦ (j.val : Fin d → ℝ)) w D.card hann
    (kernelPolynomial d D) (kernelPolynomial_degree d D)
  have hdiag (j : P) : (∑ k : P, w j * w k *
      eval (Sum.elim (j.val : Fin d → ℝ) (k.val : Fin d → ℝ)) (kernelPolynomial d D)) =
      w j ^ 2 * (∏ a ∈ D, -(a ^ 2)) := by
    rw [Finset.sum_eq_single j]
    · rw [eval_kernelPolynomial_diag]
      ring
    · intro k _ hkj
      rw [eval_kernelPolynomial_offdiag d D j.val k.val
        (hP j.val j.property k.val k.property (fun h ↦ hkj (Subtype.ext h.symm)))]
      ring
    · simp
  simp_rw [hdiag] at hz
  rw [← Finset.sum_mul] at hz
  have hc : (∏ a ∈ D, -(a ^ 2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    exact neg_ne_zero.mpr (pow_ne_zero 2 (fun h ↦ hD (h ▸ ha)))
  have hs : ∑ j : P, w j ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_right hc
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (w j))).mp hs i
    (Finset.mem_univ i)
  exact (sq_eq_zero_iff).mp hi

theorem card_le_choose (d : ℕ) (P : Finset (EuclideanSpace ℝ (Fin d)))
    (D : Finset ℝ) (hD : 0 ∉ D)
    (hP : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → dist x y ∈ D) :
    P.card ≤ Nat.choose (d + D.card) D.card := by
  classical
  have h := (evaluations_linearIndependent d P D hD hP).fintype_card_le_finrank
  simpa only [Fintype.card_coe, Subspace.dual_finrank_eq,
    JSP906.finrank_restrictTotalDegree] using h

#print axioms card_le_choose
end JSP906.BBS


/-! ## Upper -/

namespace JSP000906

/-- BBS in terms of the actual positive distance set. -/
theorem few_distances_card_le (d : ℕ) (P : Finset (EuclideanSpace ℝ (Fin d))) :
    P.card ≤ Nat.choose (d + (distinctDistances P).card) (distinctDistances P).card := by
  apply JSP906.BBS.card_le_choose d P (distinctDistances P) (zero_not_mem_distinctDistances P)
  intro x hx y hy hxy
  exact mem_distinctDistances.mpr ⟨x, hx, y, hy, hxy, rfl⟩

/-- The binomial bound forces the requested number of distinct distances. -/
theorem upper_forces (d n : ℕ) : Forces d n (Nat.choose (d + (n - 1)) (n - 1) + 1) := by
  intro P hP
  by_contra! h
  have hs : (distinctDistances P).card ≤ n - 1 := by omega
  have hb := few_distances_card_le d P
  have hm : Nat.choose (d + (distinctDistances P).card) (distinctDistances P).card ≤
      Nat.choose (d + (n - 1)) (n - 1) := by
    rw [← Nat.choose_symm_add, ← Nat.choose_symm_add]
    exact Nat.choose_le_choose d (by omega)
  omega

/-- The least forcing cardinality exists, including in dimension zero. -/
theorem hasThreshold (d n : ℕ) : HasThreshold d n := ⟨_, upper_forces d n⟩

theorem g_forces (d n : ℕ) : Forces d n (g d n) := g_spec (hasThreshold d n)

/-- Catalog lower bound. -/
theorem lower_bound (d n : ℕ) (hn : 2 ≤ n) :
    Nat.choose (d + 1) (n - 1) + 1 ≤ g d n :=
  lower_bound_of_hasThreshold hn (hasThreshold d n)

/-- Catalog upper bound. -/
theorem upper_bound (d n : ℕ) (hn : 2 ≤ n) :
    g d n ≤ Nat.choose (d + n - 1) (n - 1) + 1 := by
  have h := g_le (upper_forces d n)
  have he : d + (n - 1) = d + n - 1 := by omega
  simpa only [he] using h

/-- Both catalog bounds, with no geometric or well-definedness assumptions. -/
theorem bounds (d n : ℕ) (hn : 2 ≤ n) :
    Nat.choose (d + 1) (n - 1) + 1 ≤ g d n ∧
      g d n ≤ Nat.choose (d + n - 1) (n - 1) + 1 :=
  ⟨lower_bound d n hn, upper_bound d n hn⟩

#print axioms few_distances_card_le
#print axioms hasThreshold
#print axioms g_forces
#print axioms bounds
end JSP000906


/-! ## Limit -/

namespace JSP000906
open Filter Topology Asymptotics

/-- Fixed shifts of binomial coefficients have the same leading asymptotic. -/
theorem tendsto_shifted_choose (k c : ℕ) :
    Tendsto (fun d : ℕ => ((d + c).choose k : ℝ) / (d : ℝ)^k)
      atTop (𝓝 (1 / (k.factorial : ℝ))) := by
  have he := (isEquivalent_choose k).comp_tendsto (tendsto_add_atTop_nat c)
  have he' := he.div (IsEquivalent.refl (u := fun d : ℕ => (d : ℝ)^k))
  apply he'.tendsto_nhds_iff.mpr
  change Tendsto (fun d : ℕ => ((d + c : ℕ) : ℝ)^k / (k.factorial : ℝ) / (d : ℝ)^k)
    atTop (𝓝 (1 / (k.factorial : ℝ)))
  have hr : Tendsto (fun d : ℕ => ((d : ℝ) + c) / d) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_atTop_nhds_zero_nat.const_mul (c : ℝ))
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with d hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    field_simp
  have ht := (hr.pow k).div_const (k.factorial : ℝ)
  simpa only [Function.comp_apply, Pi.div_apply, Nat.cast_add, one_pow, div_pow, div_div, mul_comm] using ht

/-- Squeezing between the two binomial bounds yields the catalog limit. -/
theorem tendsto_of_choose_bounds (G : ℕ → ℕ) {k : ℕ} (hk : 0 < k)
    (hlo : ∀ d, (d + 1).choose k + 1 ≤ G d)
    (hhi : ∀ d, G d ≤ (d + k).choose k + 1) :
    Tendsto (fun d : ℕ => (G d : ℝ) / (d : ℝ)^k)
      atTop (𝓝 (1 / (k.factorial : ℝ))) := by
  have hz : Tendsto (fun d : ℕ => 1 / (d : ℝ)^k) atTop (𝓝 0) := by
    simpa only [one_div, inv_pow, zero_pow (by omega : k ≠ 0)] using
      ((tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun d : ℕ => 1 / (d : ℝ)) atTop (𝓝 0)).pow k)
  have lower := (tendsto_shifted_choose k 1).add hz
  have upper := (tendsto_shifted_choose k k).add hz
  simp only [add_zero] at lower upper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le lower upper
  · intro d
    dsimp only
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hlo d) (by positivity)
  · intro d
    dsimp only
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hhi d) (by positivity)

#print axioms tendsto_shifted_choose
#print axioms tendsto_of_choose_bounds
end JSP000906


/-! ## Result -/

namespace JSP000906
open Filter Topology

/-- The asymptotic formula from the catalog, for every fixed `n ≥ 2`. -/
theorem limit (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1))
      atTop (𝓝 (1 / ((n - 1).factorial : ℝ))) := by
  apply tendsto_of_choose_bounds (fun d => g d n) (by omega : 0 < n - 1)
  · exact fun d => lower_bound d n hn
  · intro d
    have he : d + (n - 1) = d + n - 1 := by omega
    simpa only [he] using upper_bound d n hn

/-- Exact specification of `g` as the least natural cardinality with the forcing property. -/
theorem g_isLeast (d n : ℕ) : IsLeast {N : ℕ | Forces d n N} (g d n) :=
  ⟨g_forces d n, fun _ h => g_le h⟩

/-- All scoped conclusions in one theorem. -/
theorem catalog_statement (n : ℕ) (hn : 2 ≤ n) :
    (∀ d : ℕ, IsLeast {N : ℕ | Forces d n N} (g d n)) ∧
    (∀ d : ℕ, Nat.choose (d + 1) (n - 1) + 1 ≤ g d n ∧
      g d n ≤ Nat.choose (d + n - 1) (n - 1) + 1) ∧
    Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1))
      atTop (𝓝 (1 / ((n - 1).factorial : ℝ))) :=
  ⟨fun d => g_isLeast d n, fun d => bounds d n hn, limit n hn⟩

#print axioms g_isLeast
#print axioms limit
#print axioms catalog_statement
end JSP000906
