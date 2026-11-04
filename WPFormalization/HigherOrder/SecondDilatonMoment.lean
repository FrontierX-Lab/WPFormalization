import WPFormalization.HigherOrder.SecondProfileGrowth
import WPFormalization.Marked.DilatonMoments

/-! The actual convergent E_p of Appendix C.2, summed from the canonical b coefficients and the existing secondProfile. -/

noncomputable section
open Set Filter

noncomputable section
open Set
namespace WP.HigherOrder

def secondDilatonMoment (p : ℕ) (Y : ℝ) : ℝ :=
  ∑' d : ℕ,canonicalDilatonCoefficient Y d*secondProfile Y (d::List.replicate p 0)

lemma secondDilatonMoment_summable (p : ℕ) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    Summable (fun d : ℕ => canonicalDilatonCoefficient Y d*secondProfile Y (d::List.replicate p 0)) := by
  obtain ⟨C,hC,hprofile⟩ := secondProfile_abs_uniform (p+1) (by omega)
  have hpoint (d : ℕ) : |canonicalDilatonCoefficient Y d*secondProfile Y (d::List.replicate p 0)| ≤
      C*(((d:ℝ)+1)^4*|canonicalDilatonCoefficient Y d|) := by
    have he := hprofile (d::List.replicate p 0) (by simp) Y hY
    simp only [List.sum_cons,List.sum_replicate,nsmul_zero,add_zero] at he
    rw [abs_mul]
    have hm := mul_le_mul_of_nonneg_left he (abs_nonneg (canonicalDilatonCoefficient Y d))
    convert hm using 1 <;> ring
  have hn : Summable (fun d : ℕ => |canonicalDilatonCoefficient Y d*secondProfile Y (d::List.replicate p 0)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hpoint
      ((canonicalDilatonCoefficient_moment_summable 4 Y hY).mul_left C)
  exact Summable.of_norm (by simpa only [Real.norm_eq_abs] using hn)

lemma secondDilatonMoment_hasSum (p : ℕ) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    HasSum (fun d : ℕ => canonicalDilatonCoefficient Y d*secondProfile Y (d::List.replicate p 0))
      (secondDilatonMoment p Y) := (secondDilatonMoment_summable p Y hY).hasSum

lemma secondDilatonMoment_abs_uniform (p : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ Y∈Icc (0:ℝ) y₀,|secondDilatonMoment p Y| ≤ C := by
  obtain ⟨Q,hQ,hprofile⟩ := secondProfile_abs_uniform (p+1) (by omega)
  obtain ⟨M,hM,hb⟩ := canonicalDilatonCoefficient_moment_tsum_uniform 4
  refine ⟨Q*M,by positivity,?_⟩
  intro Y hY
  have hpoint (d : ℕ) : |canonicalDilatonCoefficient Y d*secondProfile Y (d::List.replicate p 0)| ≤
      Q*(((d:ℝ)+1)^4*|canonicalDilatonCoefficient Y d|) := by
    have he := hprofile (d::List.replicate p 0) (by simp) Y hY
    simp only [List.sum_cons,List.sum_replicate,nsmul_zero,add_zero] at he
    rw [abs_mul]
    have hm := mul_le_mul_of_nonneg_left he (abs_nonneg (canonicalDilatonCoefficient Y d))
    convert hm using 1 <;> ring
  have hs := secondDilatonMoment_summable p Y hY
  have hn : Summable (fun d : ℕ => ‖canonicalDilatonCoefficient Y d*secondProfile Y (d::List.replicate p 0)‖) := by
    simpa only [Real.norm_eq_abs] using hs.abs
  calc
    _ ≤ ∑' d : ℕ,|canonicalDilatonCoefficient Y d*secondProfile Y (d::List.replicate p 0)| := by
      simpa only [secondDilatonMoment,Real.norm_eq_abs] using norm_tsum_le_tsum_norm hn
    _ ≤ ∑' d : ℕ,Q*(((d:ℝ)+1)^4*|canonicalDilatonCoefficient Y d|) :=
      hs.abs.tsum_le_tsum hpoint ((canonicalDilatonCoefficient_moment_summable 4 Y hY).mul_left Q)
    _ = Q*∑' d : ℕ,((d:ℝ)+1)^4*|canonicalDilatonCoefficient Y d| := tsum_mul_left
    _ ≤ Q*M := mul_le_mul_of_nonneg_left (hb Y hY) hQ.le
end WP.HigherOrder
