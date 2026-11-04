import WPFormalization.Coefficients.AdjacentLimitProof
/-! The two original endpoint consequences of the uniform adjacent-degree theorem.
The positive-codimension argument cancels the exact finite codimension before
passing to the limit; it covers every positive sublinear sequence. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients
open Filter Set
open scoped Topology

lemma adjacent_calibration_tendsto (P : PsiTheory) (ks : ℕ → ℕ)
    (hk : ∀ᶠ g in atTop, ks g < 3*g-2) :
    Tendsto (fun g => bracketAdjacentRatio P g (ks g) *
      (trigSaddle g (ks g))^2 / Real.pi^2) atTop (𝓝 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨G,hG⟩ := adjacent_limit_proof P (ε/2) (by positivity)
  obtain ⟨G',hG'⟩ := eventually_atTop.mp hk
  refine ⟨max G G',?_⟩
  intro g hg
  rw [Real.dist_eq, ←adjacentError_eq_bracketRatio]
  exact lt_of_le_of_lt (hG g ((le_max_left _ _).trans hg) _
    (hG' g ((le_max_right _ _).trans hg))) (by linarith)

lemma complexity_one_div_genus_tendsto :
    Tendsto (fun g : ℕ => (complexity g 1 : ℝ)/g) atTop (𝓝 2) := by
  have H := (tendsto_const_nhds (x := (2:ℝ))).sub
    (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
  simp only [sub_zero] at H
  apply H.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
  have hgR : (g:ℝ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  rw [adjacent_complexity_one_cast g hg]
  field_simp

lemma adjacent_small_degree_endpoint (P : PsiTheory) (ks : ℕ → ℕ)
    (hk : ∀ᶠ g in atTop, ks g < 3*g-2)
    (hks : Tendsto (fun g : ℕ => (ks g : ℝ)/g) atTop (𝓝 0)) :
    Tendsto (fun g => boundaryA P g (ks g)/boundaryA P g (ks g+1)) atTop (𝓝 4) := by
  have hsmall : Tendsto (fun g : ℕ => ((ks g : ℝ)+1)/g) atTop (𝓝 0) := by
    simpa only [zero_add] using
      (hks.add (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))).congr
        (fun g => (add_div (ks g : ℝ) 1 (g:ℝ)).symm)
  have ht : Tendsto (fun g => (trigSaddle g (ks g))^2/Real.pi^2) atTop (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    apply squeeze_zero' (Eventually.of_forall (fun g => abs_nonneg _))
    · filter_upwards [hk,eventually_ge_atTop (1:ℕ)] with g hkg hg
      exact trigSaddle_square_endpoint_bound g (ks g) hg hkg
    · simpa only [mul_zero,mul_div_assoc] using hsmall.const_mul (10/Real.pi^2)
  have hrat := (adjacent_calibration_tendsto P ks hk).div ht (by norm_num : (1:ℝ) ≠ 0)
  have hb : Tendsto (fun g => bracketAdjacentRatio P g (ks g)) atTop (𝓝 1) := by
    simp only [div_self (by norm_num : (1:ℝ) ≠ 0)] at hrat
    apply hrat.congr'
    filter_upwards [hk,eventually_ge_atTop (1:ℕ)] with g hkg hg
    have htp : 0 < trigSaddle g (ks g) := (trig_saddle_spec g (ks g) hg hkg).1.1
    change (bracketAdjacentRatio P g (ks g) *
      (trigSaddle g (ks g))^2/Real.pi^2)/((trigSaddle g (ks g))^2/Real.pi^2)=_
    field_simp [Real.pi_ne_zero,htp.ne']
  simpa only [mul_one,boundaryA_adjacent_eq_four_bracketAdjacentRatio] using hb.const_mul 4

lemma normalized_boundary_codimension_eq (P : PsiTheory) (g m : ℕ)
    (hg : 1 ≤ g) (hm : 1 ≤ m) (hmN : m ≤ 3*g-2) :
    (boundaryA P g (3*g-2-m)/boundaryA P g (3*g-2-m+1)) /
        (4*Real.pi^2*g/(5*m)) =
      (bracketAdjacentRatio P g (3*g-2-m) *
        (trigSaddle g (3*g-2-m))^2/Real.pi^2) *
      ((5/2 : ℝ)*((complexity g 1 : ℝ)/g)*saddleChi ((m:ℝ)/(complexity g 1:ℝ))) := by
  have hk : 3*g-2-m < 3*g-2 := by omega
  have hdef : 3*g-2-(3*g-2-m)=m := by omega
  have hhp : 0 < (complexity g 1 : ℝ) := by
    rw [adjacent_complexity_one_cast g hg]
    have hgR : (1:ℝ) ≤ g := by exact_mod_cast hg
    linarith
  have hgp : (g:ℝ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hmp : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hmem := adjacent_mean_parameter_mem g (3*g-2-m) hg hk.le
  rw [hdef] at hmem
  have hs := saddleChi_mul_saddleZeta _ hmem
  have ht := trigSaddle_square_saddleZeta g (3*g-2-m) hg hk
  rw [hdef] at ht
  rw [←ht] at hs
  have hs' : (trigSaddle g (3*g-2-m))^2 *
      saddleChi ((m:ℝ)/(complexity g 1:ℝ))*(complexity g 1:ℝ)=2*(m:ℝ) := by
    field_simp [hhp.ne'] at hs
    nlinarith only [hs]
  rw [boundaryA_adjacent_eq_four_bracketAdjacentRatio]
  field_simp [Real.pi_ne_zero,hgp,hmp]
  nlinarith only [congrArg (fun q : ℝ =>
    5*bracketAdjacentRatio P g (3*g-2-m)*q) hs']

lemma adjacent_positive_codimension_endpoint (P : PsiTheory) (ms : ℕ → ℕ)
    (hm : ∀ᶠ g in atTop, 1 ≤ ms g ∧ ms g ≤ 3*g-2)
    (hms : Tendsto (fun g : ℕ => (ms g : ℝ)/g) atTop (𝓝 0)) :
    Tendsto (fun g =>
      (boundaryA P g (3*g-2-ms g)/boundaryA P g (3*g-2-ms g+1)) /
        (4*Real.pi^2*g/(5*ms g))) atTop (𝓝 1) := by
  have hk : ∀ᶠ g in atTop, 3*g-2-ms g < 3*g-2 := by
    filter_upwards [hm] with g hg
    omega
  have hu : Tendsto (fun g => (ms g:ℝ)/(complexity g 1:ℝ)) atTop (𝓝 0) := by
    have H := hms.div complexity_one_div_genus_tendsto (by norm_num : (2:ℝ) ≠ 0)
    simp only [zero_div] at H
    apply H.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
    have hgp : (g:ℝ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
    change ((ms g:ℝ)/g)/((complexity g 1:ℝ)/g)=(ms g:ℝ)/(complexity g 1:ℝ)
    field_simp [hgp]
  have humem : ∀ᶠ g in atTop, (ms g:ℝ)/(complexity g 1:ℝ) ∈ Icc (0:ℝ) (3/2) := by
    filter_upwards [hm,eventually_ge_atTop (1:ℕ)] with g hmg hg
    have H := adjacent_mean_parameter_mem g (3*g-2-ms g) hg (by omega)
    simpa only [show 3*g-2-(3*g-2-ms g)=ms g by omega] using H
  have hχcont : ContinuousOn saddleChi (Icc (0:ℝ) (3/2)) := by
    obtain ⟨C,hC,hLip⟩ := saddleChi_uniform_lipschitz
    have H : LipschitzOnWith (⟨C,hC.le⟩ : NNReal) saddleChi (Icc (0:ℝ) (3/2)) := by
      apply lipschitzOnWith_iff_dist_le_mul.mpr
      intro u hu v hv
      change |saddleChi u-saddleChi v| ≤ C*|u-v|
      exact hLip v hv u hu
    exact H.continuousOn
  have hχ : Tendsto (fun g => saddleChi ((ms g:ℝ)/(complexity g 1:ℝ))) atTop (𝓝 (1/5:ℝ)) := by
    have H := (hχcont 0 (show (0:ℝ) ∈ Icc (0:ℝ) (3/2) by norm_num)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hu,humem⟩)
    simpa only [Function.comp_def,saddleChi_zero] using H
  have H := (adjacent_calibration_tendsto P (fun g => 3*g-2-ms g) hk).mul
    ((complexity_one_div_genus_tendsto.const_mul (5/2:ℝ)).mul hχ)
  norm_num only [mul_one,show (1:ℝ)*((5/2)*2*(1/5))=1 by norm_num] at H
  apply H.congr'
  filter_upwards [hm,eventually_ge_atTop (1:ℕ)] with g hmg hg
  exact (normalized_boundary_codimension_eq P g (ms g) hg hmg.1 hmg.2).symm

end WP.Coefficients

namespace WP
open Filter
open scoped Topology

lemma adjacent_endpoint_limits_proof (P : PsiTheory) :
    (∀ ks : ℕ → ℕ,
      (∀ᶠ g in atTop, ks g < 3*g-2) →
      Tendsto (fun g : ℕ => (ks g : ℝ)/g) atTop (𝓝 0) →
      Tendsto (fun g => boundaryA P g (ks g)/boundaryA P g (ks g+1)) atTop (𝓝 4)) ∧
    (∀ ms : ℕ → ℕ,
      (∀ᶠ g in atTop, 1 ≤ ms g ∧ ms g ≤ 3*g-2) →
      Tendsto (fun g : ℕ => (ms g : ℝ)/g) atTop (𝓝 0) →
      Tendsto (fun g =>
        (boundaryA P g (3*g-2-ms g)/boundaryA P g (3*g-2-ms g+1)) /
          (4*Real.pi^2*g/(5*ms g))) atTop (𝓝 1)) := by
  exact ⟨Coefficients.adjacent_small_degree_endpoint P,
    Coefficients.adjacent_positive_codimension_endpoint P⟩

end WP
