import WPFormalization.Tight.SeparatingBoundaryValues

noncomputable section
namespace WP.TightSeparating
open Set Finset
open scoped BigOperators

/-- The physical boundary vector may vary with each actual genus allocation. -/
lemma separating_tight_value_genus_sum_variable_lengths (P : PsiTheory) (k : ℕ) (L0 : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Q : ℕ,
      2 ≤ Q → Q ≤ k+1 → ∀ p : Fin Q → ℕ,
      (∀ i, 1 ≤ p i) → (∑ i, p i = 2*k) →
      ∀ s : Finset (Fin Q → ℕ),
      (∀ a ∈ s, (∀ i, Stable (a i) (p i)) ∧
        (∑ i, complexity (a i) (p i)) = complexity g 0 ∧
        (∑ i, a i)+k = g+(Q-1)) →
      ∀ Y ∈ Ico (0 : ℝ) y₀, ∀ L : (Fin Q → ℕ) → (i : Fin Q) → Fin (p i) → ℝ,
      (∀ a ∈ s, ∀ i j, 0 ≤ tightParameterScale Y*L a i j ∧ tightParameterScale Y*L a i j ≤ L0) →
      (∑ a ∈ s, ∏ i, tightShiftedPolynomial P (a i) (p i) Y (L a i)) /
          markedF P g 0 (XR Y) ≤ C*(r Y)^k/(g : ℝ)^(Q-1) := by
  obtain ⟨A,hA,G,hgen⟩ := separating_amplitude_genus_sum P k
  obtain ⟨B,hB,hbound⟩ := tight_boundary_value_upper P L0
  obtain ⟨G0,hparent⟩ := unmarked_model_sandwich_eventually P
  refine ⟨B^(2*k)*A,by positivity,max G (G0+2),?_⟩
  intro g hg Q hQ hkQ p hp hpsum s hs Y hY L hL
  have hstable : Stable g 0 := by unfold Stable;omega
  have hFpos : 0 < markedF P g 0 (XR Y) := by
    have hm := markedModel_pos_parameter g 0 hstable Y hY
    have hb := (hparent g (by omega) Y hY).1
    exact (mul_pos (by positivity : (0 : ℝ)<1/(2*Real.pi)) hm).trans_le hb
  have hprod (a : Fin Q → ℕ) (ha : a ∈ s) :
      (∏ i, tightShiftedPolynomial P (a i) (p i) Y (L a i)) ≤
        B^(2*k)*∏ i, markedF P (a i) (p i) (XR Y) := by
    calc
      _ ≤ ∏ i, B^(p i)*markedF P (a i) (p i) (XR Y) :=
        Finset.prod_le_prod₀ (fun i _ =>
          (tightShiftedPolynomial_pos P _ _ (hp i) ((hs a ha).1 i) _ hY _).le)
          (fun i _ => hbound (a i) (p i) (hp i) ((hs a ha).1 i) Y hY (L a i) (hL a ha i))
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hpsum]
  have hsum :
      (∑ a ∈ s, ∏ i, tightShiftedPolynomial P (a i) (p i) Y (L a i)) ≤
        B^(2*k)*(∑ a ∈ s, ∏ i, markedF P (a i) (p i) (XR Y)) := by
    rw [mul_sum]
    exact sum_le_sum hprod
  calc
    _ ≤ (B^(2*k)*(∑ a ∈ s, ∏ i, markedF P (a i) (p i) (XR Y)))/
        markedF P g 0 (XR Y) := div_le_div_of_nonneg_right hsum hFpos.le
    _ = B^(2*k)*((∑ a ∈ s, ∏ i, markedF P (a i) (p i) (XR Y))/
        markedF P g 0 (XR Y)) := by ring
    _ ≤ B^(2*k)*(A*(r Y)^k/(g : ℝ)^(Q-1)) :=
      mul_le_mul_of_nonneg_left (hgen g (le_of_max_le_left hg) Q hQ hkQ p hp hpsum s hs Y hY)
        (by positivity)
    _ = _ := by ring

end WP.TightSeparating
