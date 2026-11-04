import WPFormalization.Marked.GenusExtensions
import WPFormalization.Analysis.KernelWeightMoments

/-! The correction has a uniform quadratic bound. For degrees at least half the complexity this and profile bounds imply the global quartic remainder directly. -/

noncomputable section
open Set Filter
open scoped Topology

namespace WP.Analysis
lemma quadratic_degree_correction_bound (A T M D p q B : ℝ)
    (hB : 1 ≤ B) (hA : A ∈ Icc 0 B) (hT : T ∈ Icc 0 B) (hM : M ∈ Icc 0 B)
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hq : q ∈ Icc 0 p) :
    |A*(T*(D^2+(p-4)*D)+2*M*D+q*(q+5-2*p)/2)| ≤
      (B*(B*(p+5)+2*B+p*(3*p+5)/2))*(D+1)^2 := by
  have hA0 := hA.1
  have hT0 := hT.1
  have hM0 := hM.1
  have hq0 := hq.1
  have hqp := hq.2
  let F := (D+1)^2
  have hF : 1 ≤ F := by dsimp [F];nlinarith
  have hDF : D ≤ F := by dsimp [F];nlinarith [sq_nonneg D]
  have hBp : 0 ≤ B := by linarith
  have hpabs : |p-4| ≤ p+4 := by apply abs_le.mpr;constructor <;> linarith
  have hpoly : |D^2+(p-4)*D| ≤ (p+5)*F := by
    calc _ ≤ |D^2|+|(p-4)*D| := abs_add_le _ _
         _ = D^2+|p-4| *D := by rw [abs_pow,abs_of_nonneg hD,abs_mul,abs_of_nonneg hD]
         _ ≤ D^2+(p+4)*D := by gcongr
         _ ≤ _ := by dsimp [F];nlinarith [mul_nonneg hp hD,mul_nonneg hp (sq_nonneg D)]
  have hqabs : |q+5-2*p| ≤ 3*p+5 := by apply abs_le.mpr;constructor <;> linarith [hq.1,hq.2]
  have hqpoly : |q*(q+5-2*p)/2| ≤ (p*(3*p+5)/2)*F := by
    calc _ = q*|q+5-2*p|/2 := by rw [abs_div,abs_mul,abs_of_nonneg hq.1,abs_of_pos (by norm_num : (0:ℝ)<2)]
         _ ≤ p*(3*p+5)/2 := by gcongr
         _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ p*(3*p+5)/2 by positivity) (sub_nonneg.mpr hF)]
  rw [abs_mul,abs_of_nonneg hA.1]
  calc _ ≤ B*(|T*(D^2+(p-4)*D)|+|2*M*D|+|q*(q+5-2*p)/2|) := by
         apply (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) hA.1).trans
         exact mul_le_mul_of_nonneg_right hA.2 (by positivity)
       _ ≤ B*(B*((p+5)*F)+2*B*F+(p*(3*p+5)/2)*F) := by
         apply mul_le_mul_of_nonneg_left _ hBp
         apply add_le_add _ hqpoly
         apply add_le_add
         · rw [abs_mul,abs_of_nonneg hT.1]
           exact mul_le_mul hT.2 hpoly (abs_nonneg _) hBp
         · rw [abs_of_nonneg (by positivity : 0≤2*M*D)]
           exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM.2 (by norm_num)) hD).trans
             (mul_le_mul_of_nonneg_left hDF (by positivity))
       _ = _ := by dsimp [F];ring

lemma large_degree_quartic_error (c δ f D h : ℝ) (hc : 0 ≤ c) (hD : 0 ≤ D) (hh : 0<h)
    (hf : f ∈ Icc 0 1) (hδ : |δ| ≤ c*(D+1)^2) (hlarge : h/2 ≤ D) :
    |f-(1-δ/h)| ≤ (1+c)*(D+1)^4/h^2 := by
  have hF : h ≤ (D+1)^2 := by nlinarith [sq_nonneg D]
  let R := (D+1)^2/h
  have hR : 1 ≤ R := (le_div_iff₀ hh).2 (by simpa using hF)
  have hF0 : 0 ≤ (D+1)^2 := sq_nonneg _
  calc _ = |(f-1)+δ/h| := by congr 1;ring
       _ ≤ |f-1|+|δ/h| := abs_add_le _ _
       _ ≤ 1+c*(D+1)^2/h := by
         apply add_le_add
         · apply abs_le.mpr;constructor <;> linarith [hf.1,hf.2]
         · rw [abs_div,abs_of_pos hh]
           exact div_le_div_of_nonneg_right hδ hh.le
       _ ≤ (1+c)*R^2 := by
         rw [mul_div_assoc]
         change 1+c*R ≤ (1+c)*R^2
         have hR2 : R ≤ R^2 := by nlinarith
         have hR20 : 1 ≤ R^2 := by nlinarith
         nlinarith [mul_nonneg hc (sub_nonneg.mpr hR2)]
       _ = _ := by dsimp [R];field_simp <;> ring
end WP.Analysis

namespace WP
lemma degreeCorrection_uniform_quadratic_bound (p : ℕ) : ∃ C : ℝ, 0<C ∧
    ∀ d : List ℕ, d.length=p → ∀ Y ∈ Icc (0:ℝ) y₀,
      |degreeCorrection d Y| ≤ C*((d.sum:ℝ)+1)^2 := by
  obtain ⟨Ba,hBa,hAb⟩ := genusExtension_A_uniform_upper
  obtain ⟨M,hM⟩ := uniform_kernel_moments.2 1
  let B : ℝ := max 1 (max Ba M)
  have hB : 1 ≤ B := le_max_left _ _
  have hBp : 0<B := lt_of_lt_of_le zero_lt_one hB
  refine ⟨B*(B*((p:ℝ)+5)+2*B+(p:ℝ)*(3*p+5)/2),by positivity,?_⟩
  intro d hd Y hY
  have hMA : M ≤ B := (le_max_right Ba M).trans (le_max_right _ _)
  have hBA : Ba ≤ B := (le_max_left Ba M).trans (le_max_right _ _)
  have hA0 : 0 ≤ A Y := (div_pos (Analysis.barH_one_re_pos Y hY) (by norm_num : (0:ℝ)<3)).le
  have hAb' : A Y ≤ B := (hAb Y hY).trans hBA
  have hw := (Analysis.weight_hasSum_at_one Y hY).summable
  have hm := (Analysis.weight_first_moment_hasSum_at_one Y hY).summable
  have hsource := hM Y hY
  simp only [pow_one] at hsource
  have hTheta : Theta Y ≤ B := by
    have hi : Theta Y ≤ ∑'l:ℕ,(1+(l:ℝ))*weight Y l := by
      apply hw.tsum_le_tsum _ hsource.1
      intro l
      have hn := mul_nonneg (show (0:ℝ)≤l from Nat.cast_nonneg _) (weight_nonneg Y hY l)
      nlinarith
    exact (hi.trans hsource.2).trans hMA
  have hMoment : moment₁ Y ≤ B := by
    have hi : moment₁ Y ≤ ∑'l:ℕ,(1+(l:ℝ))*weight Y l := by
      apply hm.tsum_le_tsum _ hsource.1
      intro l
      nlinarith [weight_nonneg Y hY l]
    exact (hi.trans hsource.2).trans hMA
  have hT0 : 0 ≤ Theta Y := tsum_nonneg (fun l => weight_nonneg Y hY l)
  have hM0 : 0 ≤ moment₁ Y := tsum_nonneg (fun l => mul_nonneg (Nat.cast_nonneg _) (weight_nonneg Y hY l))
  have hq : (d.filter (fun k => 0<k)).length ≤ p := by simpa only [hd] using List.length_filter_le (fun k => decide (0<k)) d
  have hi := Analysis.quadratic_degree_correction_bound (A Y) (Theta Y) (moment₁ Y) (d.sum:ℝ) (p:ℝ)
    ((d.filter (fun k => 0<k)).length:ℝ) B hB ⟨hA0,hAb'⟩ ⟨hT0,hTheta⟩ ⟨hM0,hMoment⟩
    (by positivity) (by positivity) ⟨by positivity,by exact_mod_cast hq⟩
  simpa only [degreeCorrection,hd] using hi

lemma large_degree_profile_first_order (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∀ g : ℕ, 1 ≤ g → ∀ d : List ℕ, d.length=p →
      ∀ Y ∈ Icc (0:ℝ) y₀, (complexity g p:ℝ)/2 ≤ d.sum →
      |profile P g d Y-(1-degreeCorrection d Y/(complexity g p:ℝ))| ≤
        C*((d.sum:ℝ)+1)^4/(complexity g p:ℝ)^2 := by
  obtain ⟨C,hC,hbound⟩ := degreeCorrection_uniform_quadratic_bound p
  refine ⟨1+C,by positivity,?_⟩
  intro g hg d hd Y hY hlarge
  have hst : Stable g d.length := by rw [hd];unfold Stable;omega
  have hh : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hpbound := normalized_profile_bounds P g d hst (by omega) Y hY
  exact Analysis.large_degree_quartic_error C (degreeCorrection d Y) (profile P g d Y) (d.sum:ℝ) (complexity g p:ℝ)
    hC.le (by positivity) hh hpbound (hbound d hd Y hY) hlarge
end WP
