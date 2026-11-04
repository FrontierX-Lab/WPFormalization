import WPFormalization.Statements.MixedLogConcavity
import WPFormalization.Coefficients.OneBoundaryModelComparison
/-! Actual mixed-intersection log concavity yields monotone adjacent ratios
and exact finite secant bounds for the original logComparisonG. -/
noncomputable section
namespace WP.Coefficients
open Set

def adjacentLogRatio (P:PsiTheory) (g k:ℕ) : ℝ :=
  Real.log (mixedJ P g k/mixedJ P g (k+1)/(g:ℝ)^2)

lemma mixedJ_ratio_monotone (P:PsiTheory) (g:ℕ) (hg:1≤g) :
    MonotoneOn (fun k=>mixedJ P g k/mixedJ P g (k+1)) (Iio (3*g-2)) := by
  apply monotoneOn_of_le_add_one ordConnected_Iio
  intro k _ hk hk1
  have hp : 0< mixedJ P g (k+1) := mixedJ_pos_admissible P g (k+1) hg (by simp only [mem_Iio] at hk1;omega)
  have hp2 : 0< mixedJ P g (k+2) := mixedJ_pos_admissible P g (k+2) hg (by simp only [mem_Iio] at hk1;omega)
  have hcc := mixed_log_concavity P g (k+1) hg (by omega) hk1
  have hr : mixedJ P g k/mixedJ P g (k+1) ≤ mixedJ P g (k+1)/mixedJ P g (k+2) := by
    apply (div_le_div_iff₀ hp hp2).mpr
    simpa only [Nat.add_sub_cancel,Nat.add_assoc,one_add_one_eq_two,pow_two] using hcc
  simpa only [Nat.add_assoc] using hr

lemma adjacentLogRatio_monotone (P:PsiTheory) (g:ℕ) (hg:1≤g) :
    MonotoneOn (adjacentLogRatio P g) (Iio (3*g-2)) := by
  apply monotoneOn_of_le_add_one ordConnected_Iio
  intro k _ hk hk1
  have hp : 0< mixedJ P g (k+1) := mixedJ_pos_admissible P g (k+1) hg (by simp only [mem_Iio] at hk1;omega)
  have hp2 : 0< mixedJ P g (k+2) := mixedJ_pos_admissible P g (k+2) hg (by simp only [mem_Iio] at hk1;omega)
  have hcc := mixed_log_concavity P g (k+1) hg (by omega) hk1
  have hr : mixedJ P g k/mixedJ P g (k+1) ≤ mixedJ P g (k+1)/mixedJ P g (k+2) := by
    apply (div_le_div_iff₀ hp hp2).mpr
    simpa only [Nat.add_sub_cancel,Nat.add_assoc,one_add_one_eq_two,pow_two] using hcc
  unfold adjacentLogRatio
  apply Real.log_le_log
  · exact div_pos (div_pos (mixedJ_pos_admissible P g k hg (by simp only [mem_Iio] at hk;omega)) hp) (pow_pos (by exact_mod_cast (show 0<g by omega)) _)
  · apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    simpa only [Nat.add_assoc] using hr

lemma logComparisonG_increment (P:PsiTheory) (g k:ℕ) (hg:1≤g) (hk:k<3*g-2) :
    logComparisonG P g k-logComparisonG P g (k+1)=adjacentLogRatio P g k := by
  have hp : mixedJ P g k≠0 := (mixedJ_pos_admissible P g k hg hk.le).ne'
  have hp1 : mixedJ P g (k+1)≠0 := (mixedJ_pos_admissible P g (k+1) hg (by omega)).ne'
  have hpN : mixedJ P g (3*g-2)≠0 := (mixedJ_pos_admissible P g (3*g-2) hg le_rfl).ne'
  have hg0 : (g:ℝ)≠0 := by exact_mod_cast (show g≠0 by omega)
  have hnat : 2*(3*g-2-k)=2*(3*g-2-(k+1))+2 := by omega
  unfold logComparisonG adjacentLogRatio
  rw [Real.log_div hp (mul_ne_zero hpN (pow_ne_zero _ hg0)),
    Real.log_div hp1 (mul_ne_zero hpN (pow_ne_zero _ hg0)),
    Real.log_mul hpN (pow_ne_zero _ hg0),Real.log_mul hpN (pow_ne_zero _ hg0),
    Real.log_div (div_ne_zero hp hp1) (pow_ne_zero _ hg0),Real.log_div hp hp1]
  simp only [Real.log_pow]
  have hcast : ((2*(3*g-2-k):ℕ):ℝ)=((2*(3*g-2-(k+1)):ℕ):ℝ)+2 := by exact_mod_cast hnat
  push_cast at hcast
  norm_num only [Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [congrArg (fun x:ℝ=>x*Real.log g) hcast]

lemma finite_telescope_sub (G:ℕ→ℝ) (a n:ℕ) :
    ∑i∈Finset.range n,(G (a+i)-G (a+i+1))=G a-G (a+n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih];simp only [Nat.add_succ];ring

lemma adjacentLogRatio_secants (P:PsiTheory) (g k l:ℕ) (hg:1≤g)
    (hl:1≤l) (hlk:l≤k) (hk:k<3*g-2) (hkl:k+l≤3*g-2) :
    (logComparisonG P g (k-l)-logComparisonG P g k)/(l:ℝ) ≤ adjacentLogRatio P g k ∧
    adjacentLogRatio P g k ≤ (logComparisonG P g k-logComparisonG P g (k+l))/(l:ℝ) := by
  have hlp : (0:ℝ)<l := by exact_mod_cast (show 0<l by omega)
  have hm := adjacentLogRatio_monotone P g hg
  constructor
  · apply (div_le_iff₀ hlp).mpr
    have ht := finite_telescope_sub (logComparisonG P g) (k-l) l
    rw [Nat.sub_add_cancel hlk] at ht
    rw [←ht]
    calc _ = ∑i∈Finset.range l,adjacentLogRatio P g (k-l+i) := by
           apply Finset.sum_congr rfl
           intro i hi
           exact logComparisonG_increment P g (k-l+i) hg (by have hi':=Finset.mem_range.mp hi;omega)
         _ ≤ ∑i∈Finset.range l,adjacentLogRatio P g k := by
           apply Finset.sum_le_sum
           intro i hi
           apply hm (by have hi':=Finset.mem_range.mp hi;change k-l+i<3*g-2;omega) hk
           have hi':=Finset.mem_range.mp hi
           omega
         _ = _ := by simp;ring
  · apply (le_div_iff₀ hlp).mpr
    rw [←finite_telescope_sub (logComparisonG P g) k l]
    calc _ = ∑i∈Finset.range l,adjacentLogRatio P g k := by simp;ring
         _ ≤ ∑i∈Finset.range l,adjacentLogRatio P g (k+i) := by
           apply Finset.sum_le_sum
           intro i hi
           apply hm hk (by have hi':=Finset.mem_range.mp hi;change k+i<3*g-2;omega)
           omega
         _ = _ := by
           apply Finset.sum_congr rfl
           intro i hi
           exact (logComparisonG_increment P g (k+i) hg (by have hi':=Finset.mem_range.mp hi;omega)).symm
end WP.Coefficients
