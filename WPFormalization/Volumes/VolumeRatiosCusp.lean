import WPFormalization.Volumes.VolumeRatiosEndpoints
import WPFormalization.Volumes.VolumeRatiosAlgebra
import WPFormalization.Volumes.SharpExtractionProof
import WPFormalization.Analysis.VolumeProfileShifts
noncomputable section
namespace WP
open Set

lemma volume_ratios_cusp_at_extraction_density_of_model_bound (P : PsiTheory)
    (hmodel : ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ k : ℕ,
      |((2*Real.pi^2)*extractionQ g 2 k/(2*g*extractionQ g 1 k))/
        profileC (2*(k:ℝ)/complexity g 1)-1| ≤ C/g) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ, 1 ≤ n →
      |(volumeModel P g (n+1)/(2*g*volumeModel P g n))/
          profileC (2*((n-1:ℕ):ℝ)/complexity g 1)-1| ≤ C/g := by
  obtain ⟨A,hA,G₂,ha⟩ := sharp_extraction_proof P 2 (by norm_num)
  obtain ⟨B,hB,G₁,hb⟩ := sharp_extraction_proof P 1 (by norm_num)
  obtain ⟨D,hD,Gₘ,hm⟩ := hmodel
  obtain ⟨K,hK⟩ := exists_nat_gt (2*(A+B))
  let E : ℝ := 2*(A+B)
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨E+D+E*D,by positivity,max (max (max G₂ G₁) Gₘ) (K+2),?_⟩
  intro g hg n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  change |_ /profileC (2*(k:ℝ)/complexity g 1)-1| ≤ _
  have hg2 : 2 ≤ g := by omega
  have hgR : (2:ℝ) ≤ g := by exact_mod_cast hg2
  have hg0 : (0:ℝ) < g := by linarith
  have hcg : g ≤ complexity g 1 := by unfold complexity; omega
  have hcgR : (g:ℝ) ≤ complexity g 1 := by exact_mod_cast hcg
  have hch : (0:ℝ) < complexity g 1 := lt_of_lt_of_le hg0 hcgR
  have hcg2 : g ≤ complexity g 2 := by unfold complexity; omega
  have hcgR2 : (g:ℝ) ≤ complexity g 2 := by exact_mod_cast hcg2
  have hch2 : (0:ℝ) < complexity g 2 := lt_of_lt_of_le hg0 hcgR2
  have ha' : |realCoeff (iteratedDeriv 2 (Phi P g)) k/extractionQ g 2 k-1| ≤ A/g := by
    exact (ha g (by omega) k).trans ((div_le_div_iff₀ hch2 hg0).mpr (by nlinarith))
  have hb' : |realCoeff (iteratedDeriv 1 (Phi P g)) k/extractionQ g 1 k-1| ≤ B/g := by
    exact (hb g (by omega) k).trans ((div_le_div_iff₀ hch hg0).mpr (by nlinarith))
  have hsum : (A+B)/(g:ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hg0).mpr
    have hKg : (K:ℝ) ≤ g := by exact_mod_cast (show K ≤ g by omega)
    linarith
  have hsmallA : A/(g:ℝ) ≤ 1/2 := (div_le_div_of_nonneg_right (by linarith) hg0.le).trans hsum
  have hsmallB : B/(g:ℝ) ≤ 1/2 := (div_le_div_of_nonneg_right (by linarith) hg0.le).trans hsum
  have hQ1 : extractionQ g 1 k ≠ 0 := by
    intro he
    rw [he,div_zero,zero_sub,abs_neg,abs_one] at hb'
    linarith
  have hQ2 : extractionQ g 2 k ≠ 0 := by
    intro he
    rw [he,div_zero,zero_sub,abs_neg,abs_one] at ha'
    linarith
  have hV : volumeModel P g (k+1) ≠ 0 := by
    intro he
    rw [marked_realCoeff_volume,he,zero_div,zero_div,zero_sub,abs_neg,abs_one] at hb'
    linarith
  have hratio := volume_ratio_error_quotient _ _ A B g hg0 ha' hb' hsmallB
  change |_ - 1| ≤ E/g at hratio
  have hproduct := volume_ratio_error_product _ _ E D g (by linarith) hE.le hD.le
    hratio (hm g (by omega) k)
  have hd : dimension g (k+2)=dimension g (k+1)+1 := by unfold dimension; omega
  have hfac : (k.factorial:ℝ) ≠ 0 := by positivity
  have hpow : (2*Real.pi^2)^(dimension g (k+1)) ≠ (0:ℝ) := by positivity
  have hC : profileC (2*(k:ℝ)/complexity g 1) ≠ 0 :=
    (Analysis.volume_profile_C_pos _ (by positivity)).ne'
  have heq : (volumeModel P g (k+1+1)/(2*g*volumeModel P g (k+1)))/
          profileC (2*(k:ℝ)/complexity g 1) =
      (realCoeff (iteratedDeriv 2 (Phi P g)) k/extractionQ g 2 k)/
        (realCoeff (iteratedDeriv 1 (Phi P g)) k/extractionQ g 1 k)*
      (((2*Real.pi^2)*extractionQ g 2 k/(2*g*extractionQ g 1 k))/
        profileC (2*(k:ℝ)/complexity g 1)) := by
    rw [marked_realCoeff_volume,marked_realCoeff_volume]
    simp only [show k+1+1=k+2 by omega]
    rw [hd,pow_succ]
    field_simp [hQ1,hQ2,hV,hfac,hpow,hC,Real.pi_ne_zero,hg0.ne']
    <;> ring
  rw [heq]
  exact hproduct

lemma volume_ratios_cusp_positive_of_extraction_density (P : PsiTheory)
    (hstar : ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ, 1 ≤ n →
      |(volumeModel P g (n+1)/(2*g*volumeModel P g n))/
          profileC (2*((n-1:ℕ):ℝ)/complexity g 1)-1| ≤ C/g) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ, 1 ≤ n →
      |(volumeModel P g (n+1)/(2*g*volumeModel P g n))/profileC ((n:ℝ)/g)-1| ≤ C/g := by
  obtain ⟨A,hA,G,ha⟩ := hstar
  refine ⟨A+4+A*4,by positivity,max G 8,?_⟩
  intro g hg n hn
  have hg8 : 8 ≤ g := by omega
  have hg1 : (1:ℝ) ≤ g := by exact_mod_cast (show 1 ≤ g by omega)
  have hc : (complexity g 1:ℝ)=2*(g:ℝ)-1 := by
    unfold complexity
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hncast : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by rw [Nat.cast_sub hn]; norm_num
  have hC : profileC (2*((n-1:ℕ):ℝ)/complexity g 1) ≠ 0 :=
    (Analysis.volume_profile_C_pos _ (by positivity)).ne'
  have hshift := Analysis.volume_profile_C_shift_rate g n hg8 hn
  rw [←hncast,←hc] at hshift
  exact volume_ratio_change_profile _ _ _ g A 4 hg1 hA.le (by norm_num) hC
    (ha g (by omega) n hn) hshift

lemma volume_ratios_cusp_all_of_positive (P : PsiTheory)
    (hpos : ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ, 1 ≤ n →
      |(volumeModel P g (n+1)/(2*g*volumeModel P g n))/profileC ((n:ℝ)/g)-1| ≤ C/g) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ,
      |(volumeModel P g (n+1)/(2*g*volumeModel P g n))/profileC ((n:ℝ)/g)-1| ≤ C/g := by
  obtain ⟨A,hA,G₀,ha⟩ := volume_ratios_zero_cusp_add P
  obtain ⟨B,hB,G₁,hb⟩ := hpos
  refine ⟨A+B,by positivity,max G₀ G₁,?_⟩
  intro g hg n
  have hg0 : 0 ≤ (g:ℝ) := by positivity
  by_cases hn : n=0
  · subst n
    simp only [Nat.cast_zero,zero_div,zero_add]
    exact (ha g (by omega)).trans (div_le_div_of_nonneg_right (by linarith) hg0)
  · exact (hb g (by omega) n (by omega)).trans (div_le_div_of_nonneg_right (by linarith) hg0)
end WP
