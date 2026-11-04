import Mathlib

/-! A fixed weighted L1 norm bounds the unchanged infinite part of a Laplace ray. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma weighted_ray_tail_norm_bound (F : ℝ → E) (g : ℝ → ℝ) (A b q U : ℝ)
    (hA : 0 ≤ A) (hbq : b ≤ q)
    (hg : ∀ t ∈ Ioi 0, 0 ≤ g t)
    (hi : IntegrableOn (fun t:ℝ => Real.exp (-(b*t))*g t) (Ioi 0))
    (hU : (∫ t in Ioi 0,Real.exp (-(b*t))*g t) ≤ U)
    (hF : AEStronglyMeasurable F (volume.restrict (Ioi A)))
    (hbound : ∀ t ∈ Ioi A,‖F t‖ ≤ Real.exp (-(q*t))*g t) :
    IntegrableOn F (Ioi A) ∧
      ‖∫ t in Ioi A,F t‖ ≤ Real.exp (-((q-b)*A))*U := by
  let K := Real.exp (-((q-b)*A))
  have hK : 0 ≤ K := (Real.exp_pos _).le
  have his := hi.mono_set (Ioi_subset_Ioi hA)
  have hmaj : IntegrableOn (fun t:ℝ => K*(Real.exp (-(b*t))*g t)) (Ioi A) :=
    his.const_mul K
  have hp (t : ℝ) (ht : t∈Ioi A) : ‖F t‖ ≤ K*(Real.exp (-(b*t))*g t) := by
    have ht0 : t∈Ioi (0:ℝ) := hA.trans_lt ht
    calc
      _ ≤ Real.exp (-(q*t))*g t := hbound t ht
      _ = Real.exp (-((q-b)*t))*(Real.exp (-(b*t))*g t) := by
        rw [←mul_assoc,←Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by
        have := mul_le_mul_of_nonneg_left ht.le (sub_nonneg.mpr hbq)
        linarith)) (mul_nonneg (Real.exp_pos _).le (hg t ht0))
  have hFi := hmaj.mono' hF (ae_restrict_of_forall_mem measurableSet_Ioi hp)
  refine ⟨hFi,?_⟩
  calc
    _ ≤ ∫ t in Ioi A,‖F t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi A,K*(Real.exp (-(b*t))*g t) :=
      integral_mono_ae hFi.norm hmaj (ae_restrict_of_forall_mem measurableSet_Ioi hp)
    _ = K*(∫ t in Ioi A,Real.exp (-(b*t))*g t) := integral_const_mul _ _
    _ ≤ K*(∫ t in Ioi 0,Real.exp (-(b*t))*g t) := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply setIntegral_mono_set hi
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.exp_pos _).le (hg t ht)
      · exact Filter.Eventually.of_forall (Ioi_subset_Ioi hA)
    _ ≤ K*U := mul_le_mul_of_nonneg_left hU hK

end WP.Analysis
