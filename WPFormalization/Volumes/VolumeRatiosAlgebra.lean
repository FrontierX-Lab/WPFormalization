import WPFormalization.Volumes.VolumeRatiosEndpoints
noncomputable section
namespace WP

lemma volume_ratios_nonzero_of_small_error (a e : ℝ) (ha : |a-1| ≤ e) (he : e ≤ 1/2) :
    a ≠ 0 := by
  intro hz
  rw [hz,zero_sub,abs_neg,abs_one] at ha
  linarith

lemma volume_ratio_error_chain (a b c P Q t g A B : ℝ)
    (hg : 1 ≤ g) (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : t ≠ 0)
    (ha : |b/(t*a)/P-1| ≤ A/g) (hb : |c/(t*b)/Q-1| ≤ A/g)
    (hs : A/g ≤ 1/2) (hp : |P/Q-1| ≤ B/g) :
    |b^2/(a*c)-1| ≤ (4*A+B+4*A*B)/g := by
  have hg0 : 0 < g := by linarith
  have han := volume_ratios_nonzero_of_small_error _ _ ha hs
  have hbn := volume_ratios_nonzero_of_small_error _ _ hb hs
  have hane : a ≠ 0 := by intro hz; simp [hz] at han
  have hbne : b ≠ 0 := by intro hz; simp [hz] at han
  have hcne : c ≠ 0 := by intro hz; simp [hz] at hbn
  have hP : P ≠ 0 := by intro hz; simp [hz] at han
  have hQ : Q ≠ 0 := by intro hz; simp [hz] at hbn
  have hquot := volume_ratio_error_quotient _ _ A A g hg0 ha hb hs
  have hmul := volume_ratio_error_product _ _ (2*(A+A)) B g hg (by positivity) hB hquot hp
  have he : b^2/(a*c) = (b/(t*a)/P)/(c/(t*b)/Q)*(P/Q) := by
    field_simp [ht,hane,hbne,hcne,hP,hQ]
  rw [he]
  convert hmul using 1 <;> ring

lemma volume_ratio_change_profile (a P Q g A B : ℝ)
    (hg : 1 ≤ g) (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : P ≠ 0)
    (ha : |a/P-1| ≤ A/g) (hp : |P/Q-1| ≤ B/g) :
    |a/Q-1| ≤ (A+B+A*B)/g := by
  have hmul := volume_ratio_error_product _ _ A B g hg hA hB ha hp
  have he : a/Q=(a/P)*(P/Q) := by field_simp [hP]
  rw [he]
  exact hmul

lemma volume_ratios_third_of_cusp_control (P : PsiTheory)
    (hC : ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ,
      |(volumeModel P g (n+1)/(2*g*volumeModel P g n))/profileC ((n:ℝ)/g)-1| ≤ C/g)
    (hprofile : ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ, 1 ≤ n →
      |profileC (((n-1:ℕ):ℝ)/g)/profileC ((n:ℝ)/g)-1| ≤ C/g) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ, 1 ≤ n →
      |volumeModel P g n^2/(volumeModel P g (n-1)*volumeModel P g (n+1))-1| ≤ C/g := by
  obtain ⟨A,hA,G₀,ha⟩ := hC
  obtain ⟨B,hB,G₁,hb⟩ := hprofile
  obtain ⟨K,hK⟩ := exists_nat_gt (2*A)
  refine ⟨4*A+B+4*A*B,by positivity,max (max G₀ G₁) (K+2),?_⟩
  intro g hg n hn
  have hg2 : 2 ≤ g := by omega
  have hgR : (2:ℝ) ≤ g := by exact_mod_cast hg2
  have hg0 : (0:ℝ) < g := by linarith
  have hsmall : A/(g:ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hg0).mpr
    have hKg : (K:ℝ) ≤ g := by exact_mod_cast (show K ≤ g by omega)
    linarith
  apply volume_ratio_error_chain _ _ _ _ _ (2*g) g A B (by linarith) hA.le hB.le
    (by positivity) _ (ha g (by omega) n) hsmall (hb g (by omega) n hn)
  simpa only [Nat.sub_add_cancel hn] using ha g (by omega) (n-1)

lemma volume_ratios_join (P : PsiTheory)
    (hB : ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ,
      |(volumeModel P g n/volumeModel P (g-1) (n+2))/profileB ((n:ℝ)/g)-1| ≤ C/g)
    (hC : ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ,
      |(volumeModel P g (n+1)/(2*g*volumeModel P g n))/profileC ((n:ℝ)/g)-1| ≤ C/g)
    (hD : ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ, 1 ≤ n →
      |volumeModel P g n^2/(volumeModel P g (n-1)*volumeModel P g (n+1))-1| ≤ C/g) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      (∀ n : ℕ,
        |(volumeModel P g n/volumeModel P (g-1) (n+2))/profileB ((n : ℝ)/g)-1| ≤ C/g ∧
        |(volumeModel P g (n+1)/(2*g*volumeModel P g n))/profileC ((n : ℝ)/g)-1| ≤ C/g) ∧
      (∀ n : ℕ, 1 ≤ n →
        |volumeModel P g n^2/(volumeModel P g (n-1)*volumeModel P g (n+1))-1| ≤ C/g) := by
  obtain ⟨B,hB,G₀,hb⟩ := hB
  obtain ⟨C,hC,G₁,hc⟩ := hC
  obtain ⟨D,hD,G₂,hd⟩ := hD
  refine ⟨B+C+D,by positivity,max (max G₀ G₁) G₂,?_⟩
  intro g hg
  have hg0 : 0 ≤ (g:ℝ) := by positivity
  constructor
  · intro n
    constructor
    · exact (hb g (by omega) n).trans (div_le_div_of_nonneg_right (by linarith) hg0)
    · exact (hc g (by omega) n).trans (div_le_div_of_nonneg_right (by linarith) hg0)
  · intro n hn
    exact (hd g (by omega) n hn).trans (div_le_div_of_nonneg_right (by linarith) hg0)
end WP
