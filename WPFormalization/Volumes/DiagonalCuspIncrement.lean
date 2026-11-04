import WPFormalization.Analysis.ChainParameterProfile
import WPFormalization.Analysis.ChainLogarithmicError
import WPFormalization.Volumes.DiagonalChainAlgebra

/-! Exact factorial normalization of a cusp increment and its uniform
logarithmic error. The numerical cusp-ratio estimate remains an explicit
input here until the original Theorem 1.3 is supplied. -/
noncomputable section
namespace WP
open Filter
open scoped Topology

lemma diagonal_volume_pos_from_closed (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g)
    (hclosed : 0 < volumeModel P g 0) (n : ℕ) : 0 < volumeModel P g n := by
  by_cases hn : n = 0
  · simpa only [hn] using hclosed
  · exact diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)

lemma diagonal_normalized_cusp_quotient (P : PsiTheory) (g n : ℕ) (hg : 2 ≤ g)
    (hclosed : 0 < volumeModel P g 0) :
    normalizedVolume P g (n+1)/normalizedVolume P g n =
      (volumeModel P g (n+1)/volumeModel P g n)/(4*Real.pi^2*(2*(g : ℝ)+n-2)) := by
  have hs : 2*g+(n+1)-3 = (2*g+n-3)+1 := by omega
  have hc : ((2*g+n-3 : ℕ) : ℝ)+1 = 2*(g : ℝ)+n-2 := by
    rw [Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_mul]
    norm_num
    ring
  have hD : ((2*g+n-3).factorial : ℝ) ≠ 0 := by positivity
  have hV := (diagonal_volume_pos_from_closed P g hg hclosed n).ne'
  unfold normalizedVolume
  rw [hs,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,hc,pow_succ]
  field_simp

lemma diagonal_cusp_log_increment_identity (P : PsiTheory) (g n : ℕ) (hg : 2 ≤ g)
    (hclosed : 0 < volumeModel P g 0) :
    Real.log (normalizedVolume P g (n+1))-Real.log (normalizedVolume P g n)-
      Analysis.chainCuspLogProfile ((n : ℝ)/g) =
      Real.log ((volumeModel P g (n+1)/(2*g*volumeModel P g n))/WP.profileC ((n : ℝ)/g))+
        Real.log ((2*(g : ℝ)+n)/(2*g+n-2)) := by
  have hgr : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hVn := diagonal_volume_pos_from_closed P g hg hclosed n
  have hVn1 := diagonal_volume_pos_from_closed P g hg hclosed (n+1)
  have hC := Analysis.chain_profileC_pos ((n : ℝ)/g) (by positivity)
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsum : 0 < 2*(g : ℝ)+n := by positivity
  have hsum2 : 0 < 2*(g : ℝ)+n-2 := by linarith
  have hCn : 0 < 4*Real.pi^2*(2+(n : ℝ)/g) := by positivity
  have hQ : 0 < (volumeModel P g (n+1)/(2*g*volumeModel P g n))/WP.profileC ((n : ℝ)/g) := by positivity
  have hD : 0 < (2*(g : ℝ)+n)/(2*g+n-2) := div_pos hsum hsum2
  have hU : 0 < 2*WP.profileC ((n : ℝ)/g)/(4*Real.pi^2*(2+(n : ℝ)/g)) := by positivity
  have hZn : normalizedVolume P g n ≠ 0 := by unfold normalizedVolume;positivity
  have hZn1 : normalizedVolume P g (n+1) ≠ 0 := by unfold normalizedVolume;positivity
  have he : normalizedVolume P g (n+1)/normalizedVolume P g n =
      ((volumeModel P g (n+1)/(2*g*volumeModel P g n))/WP.profileC ((n : ℝ)/g))*
        (2*WP.profileC ((n : ℝ)/g)/(4*Real.pi^2*(2+(n : ℝ)/g)))*
          ((2*(g : ℝ)+n)/(2*g+n-2)) := by
    rw [diagonal_normalized_cusp_quotient P g n hg hclosed]
    field_simp
  rw [← Real.log_div hZn1 hZn,he,Real.log_mul (mul_ne_zero hQ.ne' hU.ne') hD.ne',
    Real.log_mul hQ.ne' hU.ne',Analysis.chainCuspLogProfile_eq_log_profileC _ (by positivity)]
  ring

lemma diagonal_cusp_log_increment_error (P : PsiTheory) (g n : ℕ) (hg : 2 ≤ g)
    (hclosed : 0 < volumeModel P g 0) (C : ℝ) (hC : 0 ≤ C)
    (hsmall : C/(g : ℝ) ≤ 1/2)
    (herror : |(volumeModel P g (n+1)/(2*g*volumeModel P g n))/WP.profileC ((n : ℝ)/g)-1| ≤ C/g) :
    |Real.log (normalizedVolume P g (n+1))-Real.log (normalizedVolume P g n)-
      Analysis.chainCuspLogProfile ((n : ℝ)/g)| ≤ (2*C+2)/g := by
  have hgr : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : 0 < 2*(g : ℝ)+n-2 := by linarith
  have hlog := Analysis.chain_abs_log_of_relative_error _ _ (div_nonneg hC hgr.le) hsmall herror
  have hD : (2*(g : ℝ)+n)/(2*g+n-2) = 1+2/(2*g+n-2) := by field_simp <;> ring
  have hlogD : |Real.log ((2*(g : ℝ)+n)/(2*g+n-2))| ≤ 2/g := by
    rw [hD,abs_of_nonneg (Real.log_nonneg (by have := div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hden.le;linarith))]
    have hp : 0 < 1+2/(2*(g : ℝ)+n-2) := by positivity
    have hb := Real.log_le_sub_one_of_pos hp
    have hdiv : 2/(2*(g : ℝ)+n-2) ≤ 2/(g : ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num) hgr
      linarith
    linarith only [hb,hdiv]
  rw [diagonal_cusp_log_increment_identity P g n hg hclosed]
  exact (abs_add_le _ _).trans ((add_le_add hlog hlogD).trans (by ring_nf; rfl))

end WP
