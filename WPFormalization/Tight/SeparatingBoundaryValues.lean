import WPFormalization.Tight.SeparatingGenusSum
import WPFormalization.Tight.SeparatingPositiveProduct

noncomputable section
namespace WP.TightSeparating
open Set Finset
open scoped BigOperators

/-- The original all-stable F.2 bound uniformly on a fixed scaled length box.
No component genus lower bound is introduced. -/
lemma tight_boundary_value_upper (P : PsiTheory) (L0 : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ g p : ℕ, 1 ≤ p → Stable g p →
      ∀ Y ∈ Ico (0 : ℝ) y₀, ∀ L : Fin p → ℝ,
      (∀ i, 0 ≤ tightParameterScale Y*L i ∧ tightParameterScale Y*L i ≤ L0) →
      tightShiftedPolynomial P g p Y L ≤ B^p*markedF P g p (XR Y) := by
  obtain ⟨M,hM,hbound⟩ := boundaryFactor_uniform_compact_bound L0
  let B : ℝ := max 1 M
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B,hB,?_⟩
  intro g p hp hs Y hY L hL
  have hf := markedF_pos_parameter P g p hp hs Y hY
  have hh := (tightShiftedPolynomial_bounds P g p hp hs Y hY L).2
  rw [string_flow_proof P g p hs Y hY] at hh
  have hb : (∏ i, boundaryFactor 0 (tightParameterScale Y*L i)) ≤ B^p := by
    calc
      _ ≤ ∏ _i : Fin p, B := Finset.prod_le_prod₀
        (fun i _ => (boundaryFactor_pos _ _).le)
        (fun i _ => (hbound 0 ⟨le_rfl,y₀_pos.le⟩ _ (hL i)).trans
          (le_max_right _ _))
      _ = _ := by simp
  exact (div_le_iff₀ hf).mp hh |>.trans (mul_le_mul_of_nonneg_right hb hf.le)

/-- The finite genus-summed actual tight polynomials inherit F.8 on a compact
scaled physical length box, with the same Q-1 inverse power. -/
lemma separating_tight_value_genus_sum (P : PsiTheory) (k : ℕ) (L0 : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Q : ℕ,
      2 ≤ Q → Q ≤ k+1 → ∀ p : Fin Q → ℕ,
      (∀ i, 1 ≤ p i) → (∑ i, p i = 2*k) →
      ∀ s : Finset (Fin Q → ℕ),
      (∀ a ∈ s, (∀ i, Stable (a i) (p i)) ∧
        (∑ i, complexity (a i) (p i)) = complexity g 0 ∧
        (∑ i, a i)+k = g+(Q-1)) →
      ∀ Y ∈ Ico (0 : ℝ) y₀, ∀ L : (i : Fin Q) → Fin (p i) → ℝ,
      (∀ i j, 0 ≤ tightParameterScale Y*L i j ∧ tightParameterScale Y*L i j ≤ L0) →
      (∑ a ∈ s, ∏ i, tightShiftedPolynomial P (a i) (p i) Y (L i)) /
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
      (∏ i, tightShiftedPolynomial P (a i) (p i) Y (L i)) ≤
        B^(2*k)*∏ i, markedF P (a i) (p i) (XR Y) := by
    calc
      _ ≤ ∏ i, B^(p i)*markedF P (a i) (p i) (XR Y) :=
        Finset.prod_le_prod₀ (fun i _ =>
          (tightShiftedPolynomial_pos P _ _ (hp i) ((hs a ha).1 i) _ hY _).le)
          (fun i _ => hbound (a i) (p i) (hp i) ((hs a ha).1 i) Y hY (L i) (hL i))
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hpsum]
  have hsum :
      (∑ a ∈ s, ∏ i, tightShiftedPolynomial P (a i) (p i) Y (L i)) ≤
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
