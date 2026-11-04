import WPFormalization.Tight.SeparatingScale

noncomputable section
namespace WP.TightSeparating
open Set Filter
open scoped BigOperators

/-- The component upper constant is uniform over every positive protected count
that can occur after k cuts, and every stable genus. -/
lemma component_scale_upper_fixed_cut (P : PsiTheory) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, 1 ≤ p → p ≤ 2*k →
      ∀ g : ℕ, Stable g p → ∀ Y ∈ Ico (0 : ℝ) y₀,
      markedF P g p (XR Y) ≤ C * componentScale g p Y := by
  have hex (p : ℕ) : ∃ C : ℝ, 0 < C ∧ (1 ≤ p →
      ∀ g : ℕ, Stable g p → ∀ Y ∈ Ico (0 : ℝ) y₀,
      markedF P g p (XR Y) ≤ C * componentScale g p Y) := by
    by_cases hp : 1 ≤ p
    · obtain ⟨c,C,hc,hC,h⟩ := marked_scale_sandwich_all_stable P p hp
      exact ⟨C,hC,fun _ g hs Y hY => (h g hs Y hY).2⟩
    · exact ⟨1,by norm_num,by omega⟩
  choose C hC hbound using hex
  refine ⟨1+∑ p ∈ Finset.range (2*k+1), C p,?_,?_⟩
  · have hh : 0 ≤ ∑ p ∈ Finset.range (2*k+1), C p :=
      Finset.sum_nonneg (fun p _ => (hC p).le)
    linarith
  · intro p hp hpk g hs Y hY
    have hCp : C p ≤ 1+∑ q ∈ Finset.range (2*k+1), C q := by
      have hh := Finset.single_le_sum (fun q _ => (hC q).le)
        (show p ∈ Finset.range (2*k+1) by simp;omega)
      linarith
    exact (hbound p hp g hs Y hY).trans
      (mul_le_mul_of_nonneg_right hCp (componentScale_pos g p hs Y hY).le)

/-- Original F.8 before the genera summation. Its constant and parent threshold
precede Q, every stable component genus, and the entire physical parameter range. -/
lemma separating_amplitude_product_bound (P : PsiTheory) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Q : ℕ,
      2 ≤ Q → Q ≤ k+1 → ∀ gs ps : Fin Q → ℕ,
      (∀ i, Stable (gs i) (ps i)) → (∀ i, 1 ≤ ps i) →
      (∑ i, ps i = 2*k) →
      (∑ i, complexity (gs i) (ps i) = complexity g 0) →
      ((∑ i, gs i)+k = g+(Q-1)) →
      ∀ Y ∈ Ico (0 : ℝ) y₀,
      (∏ i, markedF P (gs i) (ps i) (XR Y)) / markedF P g 0 (XR Y) ≤
        C * (r Y)^k *
          ((∏ i, gammaWeight (complexity (gs i) (ps i))) /
            gammaWeight (complexity g 0)) := by
  obtain ⟨B,hB,hupper⟩ := component_scale_upper_fixed_cut P k
  obtain ⟨c,D,hc,hD,G,hparent⟩ := unmarked_scale_sandwich_eventually P
  refine ⟨B^(k+1)*(4 : ℝ)^(k+1)/c,by positivity,G+2,?_⟩
  intro g hg Q hQ hkQ gs ps hs hps hp hh hgen Y hY
  have hg' : Stable g 0 := by unfold Stable;omega
  have hFpos : 0 < markedF P g 0 (XR Y) :=
    (mul_pos hc (componentScale_pos g 0 hg' Y hY)).trans_le
      (hparent g (by omega) Y hY).1
  have hscale := componentScale_pos g 0 hg' Y hY
  have hgamm := gammaWeight_pos (complexity g 0) (by unfold Stable complexity at *;omega)
  have hscaleprod := componentScale_product Q k g (by omega) hkQ gs ps hs hp hh hgen Y hY
  have hmarked (i : Fin Q) : 0 ≤ markedF P (gs i) (ps i) (XR Y) := by
    exact (markedF_pos_parameter P (gs i) (ps i) (hps i) (hs i) Y hY).le
  have hprod : (∏ i, markedF P (gs i) (ps i) (XR Y)) ≤
      B^Q * ∏ i, componentScale (gs i) (ps i) Y := by
    calc
      _ ≤ ∏ i, B * componentScale (gs i) (ps i) Y := by
        apply Finset.prod_le_prod₀ (fun i _ => hmarked i)
        intro i hi
        apply hupper (ps i) (hps i) _ (gs i) (hs i) Y hY
        have hh' := Finset.single_le_sum (fun j _ => Nat.zero_le (ps j))
          (Finset.mem_univ i)
        omega
      _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hBpow : B^Q ≤ B^(k+1) := pow_le_pow_right₀ hB hkQ
  have hfour : (4 : ℝ)^(k+1-Q) ≤ (4 : ℝ)^(k+1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hcomp (i : Fin Q) : 1 ≤ complexity (gs i) (ps i) := by
    have hi := hs i
    unfold Stable at hi
    unfold complexity
    omega
  have hweight : 0 ≤ (r Y)^k *
      ((∏ i, gammaWeight (complexity (gs i) (ps i))) / gammaWeight (complexity g 0)) := by
    exact mul_nonneg (pow_nonneg (r_pos Y hY).le _)
      (div_nonneg (Finset.prod_nonneg (fun i _ => (gammaWeight_pos _ (hcomp i)).le)) hgamm.le)
  apply (div_le_iff₀ hFpos).mpr
  calc
    _ ≤ B^Q * ∏ i, componentScale (gs i) (ps i) Y := hprod
    _ = (B^Q*(4 : ℝ)^(k+1-Q)) *
        ((r Y)^k*((∏ i, gammaWeight (complexity (gs i) (ps i)))/
          gammaWeight (complexity g 0))) * componentScale g 0 Y := by
      rw [hscaleprod]
      ring
    _ ≤ (B^(k+1)*(4 : ℝ)^(k+1)) *
        ((r Y)^k*((∏ i, gammaWeight (complexity (gs i) (ps i)))/
          gammaWeight (complexity g 0))) * componentScale g 0 Y := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul hBpow hfour (by positivity) (by positivity)) hweight) hscale.le
    _ ≤ _ := by
      have hh' := mul_le_mul_of_nonneg_left (hparent g (by omega) Y hY).1
        (show 0 ≤ B^(k+1)*(4 : ℝ)^(k+1)/c *
          ((r Y)^k*((∏ i, gammaWeight (complexity (gs i) (ps i)))/
            gammaWeight (complexity g 0))) by positivity)
      convert hh' using 1 <;> field_simp <;> ring

end WP.TightSeparating
