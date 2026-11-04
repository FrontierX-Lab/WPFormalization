import WPFormalization.Volumes.RatioModelIdentities
import WPFormalization.Volumes.VolumeRatiosEndpoints
import WPFormalization.Volumes.SharpExtractionProof
import WPFormalization.Analysis.VolumeProfileShifts
import WPFormalization.Volumes.VolumeRatiosAlgebra

noncomputable section
namespace WP
open Set
lemma extractionQ_genus_identity (g k : ℕ) (hg : 2 ≤ g) :
    extractionQ (g-1) 3 k =
      4*r (densityY (2*(k:ℝ)/complexity g 1))*extractionQ g 1 k := by
  have hc : complexity (g-1) 3=complexity g 1 := by unfold complexity; omega
  have hY : densityY (2*(k:ℝ)/complexity g 1) ∈ Ico 0 y₀ :=
    (Analysis.densityY_spec _ (by positivity)).1
  simp only [extractionQ,hc]
  rw [show markedModel (g-1) 3 (densityY (2*(k:ℝ)/complexity g 1)) =
      4*r (densityY (2*(k:ℝ)/complexity g 1))*
        markedModel g 1 (densityY (2*(k:ℝ)/complexity g 1)) from
      Analysis.ratioModel_genus_identity g 1 hg _ hY]
  ring

lemma profileB_extractionQ_genus_identity (g k : ℕ) (hg : 2 ≤ g) :
    profileB (2*(k:ℝ)/complexity g 1)*extractionQ (g-1) 3 k =
      (2*Real.pi^2)*extractionQ g 1 k := by
  have hY : densityY (2*(k:ℝ)/complexity g 1) ∈ Ico 0 y₀ :=
    (Analysis.densityY_spec _ (by positivity)).1
  rw [extractionQ_genus_identity g k hg,profileB,
    (stationary_root_proof _ hY).2.2.2]
  field_simp [(Delta_pos _ hY).ne']
  <;> ring

lemma volume_ratios_genus_at_extraction_density (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ, 1 ≤ n →
      |(volumeModel P g n/volumeModel P (g-1) (n+2))/
          profileB (2*((n-1:ℕ):ℝ)/complexity g 1)-1| ≤ C/g := by
  obtain ⟨A,hA,G₁,ha⟩ := sharp_extraction_proof P 1 (by norm_num)
  obtain ⟨B,hB,G₃,hb⟩ := sharp_extraction_proof P 3 (by norm_num)
  obtain ⟨K,hK⟩ := exists_nat_gt (2*(A+B))
  refine ⟨2*(A+B),by positivity,max (max G₁ (G₃+1)) (K+2),?_⟩
  intro g hg n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  change |_ / profileB (2*(k:ℝ)/complexity g 1)-1| ≤ _
  have hg2 : 2 ≤ g := by omega
  have hgR : (2:ℝ) ≤ g := by exact_mod_cast hg2
  have hg0 : (0:ℝ) < g := by linarith
  have hc : complexity (g-1) 3=complexity g 1 := by unfold complexity; omega
  have hcg : g ≤ complexity g 1 := by unfold complexity; omega
  have hcgR : (g:ℝ) ≤ complexity g 1 := by exact_mod_cast hcg
  have hch : (0:ℝ) < complexity g 1 := lt_of_lt_of_le hg0 hcgR
  have ha' : |realCoeff (iteratedDeriv 1 (Phi P g)) k/extractionQ g 1 k-1| ≤ A/g := by
    exact (ha g (by omega) k).trans ((div_le_div_iff₀ hch hg0).mpr (by nlinarith))
  have hb' : |realCoeff (iteratedDeriv 3 (Phi P (g-1))) k/extractionQ (g-1) 3 k-1| ≤ B/g := by
    have ht := hb (g-1) (by omega) k
    rw [hc] at ht
    exact ht.trans ((div_le_div_iff₀ hch hg0).mpr (by nlinarith))
  have hsum : (A+B)/(g:ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hg0).mpr
    have hKg : (K:ℝ) ≤ g := by exact_mod_cast (show K ≤ g by omega)
    linarith
  have hsmallA : A/(g:ℝ) ≤ 1/2 := (div_le_div_of_nonneg_right (by linarith) hg0.le).trans hsum
  have hsmallB : B/(g:ℝ) ≤ 1/2 := (div_le_div_of_nonneg_right (by linarith) hg0.le).trans hsum
  have hQ : extractionQ g 1 k ≠ 0 := by
    intro he
    rw [he,div_zero,zero_sub,abs_neg,abs_one] at ha'
    linarith
  have hQ' : extractionQ (g-1) 3 k ≠ 0 := by
    intro he
    rw [he,div_zero,zero_sub,abs_neg,abs_one] at hb'
    linarith
  have hV : volumeModel P (g-1) (k+3) ≠ 0 := by
    intro he
    rw [marked_realCoeff_volume,he,zero_div,zero_div,zero_sub,abs_neg,abs_one] at hb'
    linarith
  have hratio := volume_ratio_error_quotient _ _ A B g hg0 ha' hb' hsmallB
  have hY : densityY (2*(k:ℝ)/complexity g 1) ∈ Ico 0 y₀ :=
    (Analysis.densityY_spec _ (by positivity)).1
  have hd : dimension g (k+1)=dimension (g-1) (k+3)+1 := by unfold dimension; omega
  have hfac : (k.factorial:ℝ) ≠ 0 := by positivity
  have hpow : (2*Real.pi^2)^(dimension (g-1) (k+3)) ≠ (0:ℝ) := by positivity
  have hD : Delta (densityY (2*(k:ℝ)/complexity g 1)) ≠ 0 := (Delta_pos _ hY).ne'
  have heq : (volumeModel P g (k+1)/volumeModel P (g-1) (k+1+2))/
          profileB (2*(k:ℝ)/complexity g 1) =
      (realCoeff (iteratedDeriv 1 (Phi P g)) k/extractionQ g 1 k)/
        (realCoeff (iteratedDeriv 3 (Phi P (g-1))) k/extractionQ (g-1) 3 k) := by
    rw [marked_realCoeff_volume,marked_realCoeff_volume,
      extractionQ_genus_identity g k hg2,profileB,
      (stationary_root_proof _ hY).2.2.2]
    simp only [show k+1+2=k+3 by omega]
    rw [hd,pow_succ]
    field_simp [hQ,hQ',hV,hfac,hpow,hD,Real.pi_ne_zero]
    <;> ring
  rw [heq]
  exact hratio

lemma volume_ratios_genus_positive_cusps (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ, 1 ≤ n →
      |(volumeModel P g n/volumeModel P (g-1) (n+2))/profileB ((n:ℝ)/g)-1| ≤ C/g := by
  obtain ⟨A,hA,G,ha⟩ := volume_ratios_genus_at_extraction_density P
  refine ⟨A+16+A*16,by positivity,max G 8,?_⟩
  intro g hg n hn
  have hg8 : 8 ≤ g := by omega
  have hg1 : (1:ℝ) ≤ g := by exact_mod_cast (show 1 ≤ g by omega)
  have hc : (complexity g 1:ℝ)=2*(g:ℝ)-1 := by
    unfold complexity
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hncast : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by rw [Nat.cast_sub hn]; norm_num
  have hY : densityY (2*((n-1:ℕ):ℝ)/complexity g 1) ∈ Ico 0 y₀ :=
    (Analysis.densityY_spec _ (by positivity)).1
  have hB : profileB (2*((n-1:ℕ):ℝ)/complexity g 1) ≠ 0 := by
    unfold profileB
    exact div_ne_zero (pow_ne_zero _ Real.pi_ne_zero)
      (mul_ne_zero (by norm_num) (Delta_pos _ hY).ne')
  have hshift := Analysis.volume_profile_B_shift_rate g n hg8 hn
  rw [←hncast,←hc] at hshift
  exact volume_ratio_change_profile _ _ _ g A 16 hg1 hA.le (by norm_num) hB
    (ha g (by omega) n hn) hshift

lemma volume_ratios_genus_all_cusps (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ,
      |(volumeModel P g n/volumeModel P (g-1) (n+2))/profileB ((n:ℝ)/g)-1| ≤ C/g := by
  obtain ⟨A,hA,G₀,ha⟩ := volume_ratios_zero_cusp_genus P
  obtain ⟨B,hB,G₁,hb⟩ := volume_ratios_genus_positive_cusps P
  refine ⟨A+B,by positivity,max G₀ G₁,?_⟩
  intro g hg n
  have hg0 : 0 ≤ (g:ℝ) := by positivity
  by_cases hn : n=0
  · subst n
    simp only [Nat.cast_zero,zero_div]
    exact (ha g (by omega)).trans (div_le_div_of_nonneg_right (by linarith) hg0)
  · exact (hb g (by omega) n (by omega)).trans (div_le_div_of_nonneg_right (by linarith) hg0)
end WP
