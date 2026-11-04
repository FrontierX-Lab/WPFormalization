import WPFormalization.Marked.SecondProfileCanonical
import WPFormalization.Marked.SecondProfileLarge

/-! The complete Appendix C.1 profile remainder. The stronger all-degree theorem implies the original h^(1/8) range with the same sextic cubic-error scale. -/

noncomputable section
open Set

namespace WP
lemma second_profile_all_degrees_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ d : List ℕ,d.length=p →∀ Y∈Icc (0:ℝ) y₀,
      |profile P g d Y-(1-degreeCorrection d Y/(complexity g p:ℝ)+
        HigherOrder.secondProfile Y d/(complexity g p:ℝ)^2)| ≤
        C*((d.sum:ℝ)+1)^6/(complexity g p:ℝ)^3 := by
  obtain ⟨Cs,hCs,Gs,hstep⟩ := second_degree_adjacent_small_index P p hp
  obtain ⟨Cb,hCb,hbig⟩ := second_profile_large_degrees P p hp
  refine ⟨Cs+Cb,by positivity,max 2 Gs,?_⟩
  intro g hg d hd Y hY
  have hg2 : 2 ≤ g := (le_max_left _ _).trans hg
  have hgS : Gs ≤ g := (le_max_right _ _).trans hg
  have hhp : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  by_cases hsmall : (d.sum:ℝ) ≤ (complexity g p:ℝ)/2
  · have he := second_profile_canonical_small P p hp g (by omega) Y hY Cs hCs.le
      (fun e he hs i hi => hstep g hgS e he hs i hi Y hY) d hd hsmall
    exact he.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith : Cs ≤ Cs+Cb) (by positivity)) (by positivity))
  · have he := hbig g (by omega) d hd (by linarith) Y hY
    exact he.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith : Cb ≤ Cs+Cb) (by positivity)) (by positivity))

lemma second_profile_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ d : List ℕ,d.length=p →
      (d.sum:ℝ) ≤ Real.rpow (complexity g p:ℝ) (1/8:ℝ) →∀ Y∈Icc (0:ℝ) y₀,
      |profile P g d Y-(1-degreeCorrection d Y/(complexity g p:ℝ)+
        HigherOrder.secondProfile Y d/(complexity g p:ℝ)^2)| ≤
        C*((d.sum:ℝ)+1)^6/(complexity g p:ℝ)^3 := by
  obtain ⟨C,hC,G,hproof⟩ := second_profile_all_degrees_proof P p hp
  exact ⟨C,hC,G,fun g hg d hd _ Y hY => hproof g hg d hd Y hY⟩
end WP
