import Mathlib
/-! A compact finite subcover combines local uniform Gaussian Gevrey errors. The error function and native budget stay fixed, all smaller cutoffs are retained, and constants precede all states and truncation orders. The proof merges local radii/rates by finite positive products and error constants by finite sums. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis

lemma finite_positive_product_le_factor {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i)
    (i : ι) (hi : i ∈ s) :
    0 < ∏ j ∈ s, min 1 (r j) ∧ (∏ j ∈ s, min 1 (r j)) ≤ r i := by
  have hp : 0 < ∏ j ∈ s, min 1 (r j) := by
    exact Finset.prod_pos (fun j hj => lt_min zero_lt_one (hr j hj))
  refine ⟨hp,?_⟩
  have he : (∏ j ∈ s.erase i, min 1 (r j)) ≤ 1 :=
    Finset.prod_le_one₀ (fun j hj => (lt_min zero_lt_one (hr j (Finset.mem_of_mem_erase hj))).le)
      (fun j hj => min_le_left _ _)
  have hmin : 0 ≤ min 1 (r i) := (lt_min zero_lt_one (hr i hi)).le
  rw [←Finset.mul_prod_erase s (fun j => min 1 (r j)) hi]
  exact (mul_le_of_le_one_right hmin he).trans (min_le_right _ _)

lemma compact_gaussian_remainder_patching {α : Type*} [TopologicalSpace α]
    (K : Set α) (hK : IsCompact K)
    (err : α → ℝ → ℝ → ℕ → ℕ → ℝ) (budget : ℝ → ℕ → ℕ → Prop)
    (hlocal : ∀ x ∈ K, ∃ (U : Set α) (ρ C B : ℝ), IsOpen U ∧ x ∈ U ∧
      0 < ρ ∧ 0 < C ∧ 0 < B ∧
      ∀ τ ∈ Ioc (0 : ℝ) ρ, ∃ c a H : ℝ, 0 < c ∧ 0 < a ∧ 0 < H ∧
        ∀ y ∈ K ∩ U, ∀ h : ℝ, H ≤ h → ∀ J N : ℕ, N ≤ J →
          budget h J N → (N : ℝ) ≤ c * Real.sqrt h →
          err y τ h J N ≤ C * B^(N+1) * ((N+1).factorial : ℝ)^2 / h^(N+1) +
            C * Real.exp (-a * Real.sqrt h)) :
    ∃ ρ C B : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < B ∧
      ∀ τ ∈ Ioc (0 : ℝ) ρ, ∃ c a H : ℝ, 0 < c ∧ 0 < a ∧ 0 < H ∧
        ∀ y ∈ K, ∀ h : ℝ, H ≤ h → ∀ J N : ℕ, N ≤ J →
          budget h J N → (N : ℝ) ≤ c * Real.sqrt h →
          err y τ h J N ≤ C * B^(N+1) * ((N+1).factorial : ℝ)^2 / h^(N+1) +
            C * Real.exp (-a * Real.sqrt h) := by
  classical
  choose U ρ C B hU hUx hρ hC hB hest using fun x : K => hlocal x x.property
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => U x) hU (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hUx ⟨x,hx⟩⟩)
  let ρ0 : ℝ := ∏ x ∈ t, min 1 (ρ x)
  let C0 : ℝ := 1 + ∑ x ∈ t, C x
  let B0 : ℝ := 1 + ∑ x ∈ t, B x
  have hρ0 : 0 < ρ0 := Finset.prod_pos (fun x hx => lt_min zero_lt_one (hρ x))
  have hC0 : 0 < C0 := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun x hx => (hC x).le))
  have hB0 : 0 < B0 := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun x hx => (hB x).le))
  have hρle (x : K) (hx : x ∈ t) : ρ0 ≤ ρ x :=
    (finite_positive_product_le_factor t ρ (fun y hy => hρ y) x hx).2
  have hCle (x : K) (hx : x ∈ t) : C x ≤ C0 := by
    have he : C x ≤ ∑ y ∈ t, C y := Finset.single_le_sum (fun y hy => (hC y).le) hx
    dsimp [C0]
    linarith
  have hBle (x : K) (hx : x ∈ t) : B x ≤ B0 := by
    have he : B x ≤ ∑ y ∈ t, B y := Finset.single_le_sum (fun y hy => (hB y).le) hx
    dsimp [B0]
    linarith
  refine ⟨ρ0,C0,B0,hρ0,hC0,hB0,?_⟩
  intro τ hτ
  have hτx (x : K) (hx : x ∈ t) : τ ∈ Ioc (0 : ℝ) (ρ x) := ⟨hτ.1,hτ.2.trans (hρle x hx)⟩
  choose c a H hc ha hH he using fun x : {x : K // x ∈ t} => hest x.val τ (hτx x.val x.property)
  let c0 : ℝ := ∏ x : {x : K // x ∈ t}, min 1 (c x)
  let a0 : ℝ := ∏ x : {x : K // x ∈ t}, min 1 (a x)
  let H0 : ℝ := 1 + ∑ x : {x : K // x ∈ t}, H x
  have hc0 : 0 < c0 := Finset.prod_pos (fun x hx => lt_min zero_lt_one (hc x))
  have ha0 : 0 < a0 := Finset.prod_pos (fun x hx => lt_min zero_lt_one (ha x))
  have hH0 : 0 < H0 := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun x hx => (hH x).le))
  have hcle (x : {x : K // x ∈ t}) : c0 ≤ c x :=
    (finite_positive_product_le_factor Finset.univ c (fun y hy => hc y) x (Finset.mem_univ _)).2
  have hale (x : {x : K // x ∈ t}) : a0 ≤ a x :=
    (finite_positive_product_le_factor Finset.univ a (fun y hy => ha y) x (Finset.mem_univ _)).2
  have hHle (x : {x : K // x ∈ t}) : H x ≤ H0 := by
    have hh : H x ≤ ∑ y : {x : K // x ∈ t}, H y :=
      Finset.single_le_sum (fun y hy => (hH y).le) (Finset.mem_univ _)
    change H x ≤ 1 + ∑ y : {x : K // x ∈ t}, H y
    linarith only [hh]
  refine ⟨c0,a0,H0,hc0,ha0,hH0,?_⟩
  intro y hy h hh J N hNJ hbudget hN
  obtain ⟨x,hxt,hyU⟩ := mem_iUnion₂.mp (ht hy)
  let xi : {x : K // x ∈ t} := ⟨x,hxt⟩
  have hhpos : 0 < h := hH0.trans_le hh
  have hNx : (N : ℝ) ≤ c xi * Real.sqrt h :=
    hN.trans (mul_le_mul_of_nonneg_right (hcle xi) (Real.sqrt_nonneg h))
  have herr := he xi y ⟨hy,hyU⟩ h ((hHle xi).trans hh) J N hNJ hbudget hNx
  refine herr.trans (add_le_add ?_ ?_)
  · apply div_le_div_of_nonneg_right _ (pow_nonneg hhpos.le _)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul (hCle x hxt) (pow_le_pow_left₀ (hB x).le (hBle x hxt) _)
      (pow_nonneg (hB x).le _) hC0.le
  · exact mul_le_mul (hCle x hxt)
      (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right (hale xi) (Real.sqrt_nonneg h)]))
      (Real.exp_pos _).le hC0.le
end WP.Analysis
