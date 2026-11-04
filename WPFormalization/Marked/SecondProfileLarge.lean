import WPFormalization.HigherOrder.SecondProfileGrowth

/-! Actual profile bounds and the true coefficient growth control degrees above half the complexity. -/

noncomputable section
open Set

noncomputable section
open Set
namespace WP.Analysis
lemma large_degree_sextic_error (cδ ce D h f δ e : ℝ)
    (hcδ : 0 ≤ cδ) (hce : 0 ≤ ce) (hD : 0 ≤ D) (hh : 0<h)
    (hf : f∈Icc 0 1) (hδ : |δ| ≤ cδ*(D+1)^2) (he : |e| ≤ ce*(D+1)^4)
    (hlarge : h/2 ≤ D) :
    |f-(1-δ/h+e/h^2)| ≤ (1+cδ+ce)*(D+1)^6/h^3 := by
  let R : ℝ := (D+1)^2/h
  have hR : 1 ≤ R := (le_div_iff₀ hh).2 (by nlinarith [sq_nonneg D])
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hR13 : R ≤ R^3 := by simpa only [pow_one] using (pow_le_pow_right₀ hR (by norm_num) : R^1 ≤ R^3)
  have hR23 : R^2 ≤ R^3 := pow_le_pow_right₀ hR (by norm_num)
  have hR3 : 1 ≤ R^3 := one_le_pow₀ hR
  have hdelta : |δ/h| ≤ cδ*R := by
    rw [abs_div,abs_of_pos hh]
    convert div_le_div_of_nonneg_right hδ hh.le using 1 <;> dsimp [R] <;> ring
  have hepsilon : |e/h^2| ≤ ce*R^2 := by
    rw [abs_div,abs_pow,abs_of_pos hh]
    convert div_le_div_of_nonneg_right he (sq_nonneg h) using 1 <;> dsimp [R] <;> ring
  have heq : f-(1-δ/h+e/h^2)=((f-1)+δ/h)-e/h^2 := by ring
  rw [heq]
  calc
    _ ≤ |f-1|+|δ/h|+|e/h^2| := (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 1+cδ*R+ce*R^2 := add_le_add (add_le_add (by apply abs_le.mpr;constructor <;> linarith [hf.1,hf.2]) hdelta) hepsilon
    _ ≤ (1+cδ+ce)*R^3 := by
      nlinarith [mul_le_mul_of_nonneg_left hR13 hcδ,mul_le_mul_of_nonneg_left hR23 hce]
    _ = _ := by dsimp [R];field_simp <;> ring
end WP.Analysis
namespace WP
lemma second_profile_large_degrees (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∀ g : ℕ,1 ≤ g → ∀ d : List ℕ,d.length=p →
      (complexity g p:ℝ)/2 ≤ (d.sum:ℝ) → ∀ Y∈Icc (0:ℝ) y₀,
      |profile P g d Y-(1-degreeCorrection d Y/(complexity g p:ℝ)+
        HigherOrder.secondProfile Y d/(complexity g p:ℝ)^2)| ≤
        C*((d.sum:ℝ)+1)^6/(complexity g p:ℝ)^3 := by
  obtain ⟨Cδ,hCδ,hδ⟩ := degreeCorrection_uniform_quadratic_bound p
  obtain ⟨Ce,hCe,he⟩ := HigherOrder.secondProfile_abs_uniform p hp
  refine ⟨1+Cδ+Ce,by positivity,?_⟩
  intro g hg d hd hlarge Y hY
  have hhp : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hprof : profile P g d Y∈Icc (0:ℝ) 1 := by
    simpa only [profile,Set.mem_Icc] using normalized_profile_bounds P g d
      (by rw [hd];unfold Stable;omega) (by rw [hd];exact hp) Y hY
  exact Analysis.large_degree_sextic_error Cδ Ce (d.sum:ℝ) (complexity g p:ℝ)
    (profile P g d Y) (degreeCorrection d Y) (HigherOrder.secondProfile Y d)
    hCδ.le hCe.le (Nat.cast_nonneg _) hhp hprof (hδ d hd Y hY) (he d hd Y hY) hlarge
end WP
