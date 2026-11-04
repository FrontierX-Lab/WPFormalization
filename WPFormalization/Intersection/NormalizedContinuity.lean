import WPFormalization.Intersection.CanonicalBackground
import WPFormalization.Analysis.DeflatedKernel
import WPFormalization.Analysis.HarmonicSumProbability
/-! Continuity of the actual finite-background amplitudes through the critical
endpoint, followed by continuity of their true harmonic normalization. The
canonical closed-interval identity handles the endpoint without assuming a
limit for the original piecewise definition. -/
noncomputable section
open Set
namespace WP

lemma normalizedBackgroundTime_continuous (i : ℕ) :
    Continuous (fun Y : Icc (0:ℝ) y₀ => normalizedBackgroundTime (Y:ℝ) i) := by
  have hc := Analysis.parameter_coeff_continuous
    (fun Y : Icc (0:ℝ) y₀ => barK (Y:ℝ)) 1 (by norm_num)
    (fun Y => (barK_differentiable (Y:ℝ)).differentiableOn)
    (Analysis.barK_joint_continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) (i+1)
  exact continuous_const.mul (Complex.continuous_re.comp hc)

lemma finiteBackgroundAmplitude_continuous {E : Type*} [TopologicalSpace E]
    (P : PsiTheory) (g : ℕ) (d : List ℤ) {N : ℕ} (B m : ℕ)
    (t : E → Fin N → ℝ) (ht : ∀ i, Continuous (fun x => t x i)) :
    Continuous (fun x => finiteBackgroundAmplitude P g d B m (t x)) := by
  unfold finiteBackgroundAmplitude
  apply continuous_const.mul
  apply continuous_finsetSum
  intro l hl
  apply continuous_const.mul
  apply continuous_finsetProd
  intro i hi
  exact ((ht i).pow (l i)).div_const _

lemma normalized_continuous_valid (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (hd : d.sum ≤ dimension g d.length) :
    Continuous (fun Y : Icc (0:ℝ) y₀ => normalized P g d (Y:ℝ)) := by
  have hf := finiteBackgroundAmplitude_continuous P g (d.map Int.ofNat)
    (deficit g d) (deficit g d)
    (fun Y : Icc (0:ℝ) y₀ => fun i : Fin (deficit g d+1) =>
      normalizedBackgroundTime (Y:ℝ) i.val)
    (fun i => normalizedBackgroundTime_continuous i.val)
  apply hf.congr
  intro Y
  exact finiteBackgroundAmplitude_normalized_canonical P g d Y Y.property hs hd
    (deficit g d+1) (deficit g d) (by omega) (by omega) le_rfl

lemma normalized_continuous (P : PsiTheory) (g : ℕ) (d : List ℕ) :
    Continuous (fun Y : Icc (0:ℝ) y₀ => normalized P g d (Y:ℝ)) := by
  by_cases hs : Stable g d.length
  · by_cases hd : d.sum ≤ dimension g d.length
    · exact normalized_continuous_valid P g d hs hd
    · have he : (fun Y : Icc (0:ℝ) y₀ => normalized P g d (Y:ℝ)) = fun _ => 0 := by
        funext Y
        exact normalized_excess P g d Y (by omega)
      rw [he]
      exact continuous_const
  · have he : (fun Y : Icc (0:ℝ) y₀ => normalized P g d (Y:ℝ)) = fun _ => 0 := by
      funext Y
      exact normalized_unstable P g d Y hs
    rw [he]
    exact continuous_const

lemma harmonicCoeff_continuous (h m : ℕ) :
    Continuous (fun Y : Icc (0:ℝ) y₀ => harmonicCoeff (Y:ℝ) h m) := by
  have hA : Continuous (fun Y : Icc (0:ℝ) y₀ => (barH (Y:ℝ) 1).re) :=
    Complex.continuous_re.comp (Analysis.barH_joint_continuous.comp
      (continuous_id.prodMk continuous_const))
  have hf := (Analysis.harmonicSumMass_continuous h m).div (hA.pow h)
    (fun Y => pow_ne_zero _ (Analysis.barH_one_re_pos Y Y.property).ne')
  apply hf.congr
  intro Y
  change harmonicSumMass (Y:ℝ) h m / (barH (Y:ℝ) 1).re^h = harmonicCoeff (Y:ℝ) h m
  rw [Analysis.harmonicSumMass_eq_normalized_coeff Y Y.property h m]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (Analysis.barH_one_re_pos Y Y.property).ne')

lemma model_continuous (g : ℕ) (d : List ℕ) :
    Continuous (fun Y : Icc (0:ℝ) y₀ => model g d (Y:ℝ)) := by
  exact continuous_const.mul (harmonicCoeff_continuous _ _)

lemma ratio_continuous (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) :
    Continuous (fun Y : Icc (0:ℝ) y₀ => ratio P g d (Y:ℝ)) := by
  apply (normalized_continuous P g d).div (model_continuous g d)
  intro Y
  have hh : 0 < complexity g d.length := by unfold complexity;unfold Stable at hs;omega
  have hp : 0 < model g d Y := by
    unfold model
    exact mul_pos (div_pos (mul_pos (by positivity)
      (Real.Gamma_pos_of_pos (by exact_mod_cast hh))) (by positivity))
      (harmonicCoeff_pos Y _ _ hh Y.property)
  exact hp.ne'
end WP
