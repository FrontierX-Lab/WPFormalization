import WPFormalization.External.TightMoments
import WPFormalization.Tight.GeneratingFunctions
import WPFormalization.Volumes.CriticalModelLens
/-! The actual cusp specialization of the classical generic moment transform.
The root, moments, physical normalization and coefficient identity are proved
locally; no Y-dependent specialization is an external field. -/
noncomputable section
namespace WP.TightMoments
open Set Filter MeasureTheory PositiveConvolution External
open scoped Topology

lemma classicalI0Kernel_zero (r:ℂ):classicalI0Kernel 0 r=1:=by
  unfold classicalI0Kernel
  simp only [Complex.ofReal_zero,zero_pow (by omega:2≠0),zero_mul,zero_div]
  rw [tsum_eq_single 0]
  · norm_num
  · intro j hj
    simp [hj]

lemma classicalWeightedKernel_dirac_zero (r:ℂ):
    classicalWeightedKernel (Measure.dirac (0:ℝ)) r=1:=by
  rw [classicalWeightedKernel,integral_dirac,classicalI0Kernel_zero]
lemma classicalRootKernel_dirac_zero (r t:ℂ):
    classicalRootKernel (Measure.dirac (0:ℝ)) r t=
      X ((2*Real.pi^2:ℝ)*r)/(2*Real.pi^2:ℝ)-t:=by
  rw [classicalRootKernel,classicalWeightedKernel_dirac_zero,mul_one]
lemma classicalMomentGerm_dirac_zero (R:ℂ→ℂ) (j:ℕ) (t:ℂ):
    classicalMomentGerm (Measure.dirac (0:ℝ)) R j t=
      (2*Real.pi^2:ℝ)^j*iteratedDeriv (j+1) X ((2*Real.pi^2:ℝ)*R t):=by
  have hc:((2*Real.pi^2:ℝ):ℂ)≠0:=by exact_mod_cast (show (2*Real.pi^2:ℝ)≠0 by positivity)
  unfold classicalMomentGerm
  simp_rw [classicalRootKernel_dirac_zero]
  have he:(fun r:ℂ=>X ((2*Real.pi^2:ℝ)*r)/(2*Real.pi^2:ℝ)-t)=
      (fun r:ℂ=>-t+X ((2*Real.pi^2:ℝ)*r)/(2*Real.pi^2:ℝ)):=by funext r;ring
  rw [he,iteratedDeriv_const_add (by omega) (-t),iteratedDeriv_div_const,
    Analysis.iteratedDeriv_comp_mul_left,pow_succ]
  field_simp

def physicalCuspRoot (P:PsiTheory) (t:ℂ):ℂ:=planarInverse P ((2*Real.pi^2:ℝ)*t)/(2*Real.pi^2:ℝ)
lemma physicalCuspRoot_zero (P:PsiTheory):physicalCuspRoot P 0=0:=by
  simp only [physicalCuspRoot,mul_zero,planarInverse_zero,zero_div]
lemma physicalCuspRoot_analyticAt (P:PsiTheory):AnalyticAt ℂ (physicalCuspRoot P) 0:=by
  have hx:‖(0:ℂ)‖<xCritical:=by simpa only [norm_zero] using Analysis.xCritical_pos_parameter
  have ha:AnalyticAt ℂ (fun t:ℂ=>(2*Real.pi^2:ℝ)*t) 0:=analyticAt_const.mul analyticAt_id
  have hb:AnalyticAt ℂ (planarInverse P) ((2*Real.pi^2:ℝ)*(0:ℂ)):=by simpa only [mul_zero] using planarInverse_analyticAt P 0 hx
  exact (hb.comp ha).div_const

lemma physicalCuspRoot_root (P:PsiTheory):
    ∀ᶠt:ℂ in 𝓝 0,classicalRootKernel (Measure.dirac (0:ℝ)) (physicalCuspRoot P t) t=0:=by
  have hc:((2*Real.pi^2:ℝ):ℂ)≠0:=by exact_mod_cast (show (2*Real.pi^2:ℝ)≠0 by positivity)
  have ht:Tendsto (fun t:ℂ=>(2*Real.pi^2:ℝ)*t) (𝓝 0) (𝓝 0):=by
    have ha:Continuous (fun t:ℂ=>(2*Real.pi^2:ℝ)*t):=continuous_const.mul continuous_id
    simpa only [mul_zero] using (ha.continuousAt (x := (0:ℂ))).tendsto
  filter_upwards [ht.eventually (Metric.ball_mem_nhds (0:ℂ) Analysis.xCritical_pos_parameter)] with t ht
  rw [classicalRootKernel_dirac_zero,physicalCuspRoot,mul_div_cancel₀ _ hc,
    X_planarInverse_eq P _ (by simpa only [Metric.mem_ball,dist_zero_right] using ht)]
  field_simp
  <;>ring
lemma physicalCuspRoot_moments (P:PsiTheory) (j:ℕ) (t:ℂ):
    classicalMomentGerm (Measure.dirac (0:ℝ)) (physicalCuspRoot P) j t=
      scaledPlaneMoments P j ((2*Real.pi^2:ℝ)*t):=by
  have hc:((2*Real.pi^2:ℝ):ℂ)≠0:=by exact_mod_cast (show (2*Real.pi^2:ℝ)≠0 by positivity)
  rw [classicalMomentGerm_dirac_zero,physicalCuspRoot,mul_div_cancel₀ _ hc]
  rfl
lemma pi_dirac_zero (k:ℕ):
    Measure.pi (fun _:Fin k=>Measure.dirac (0:ℝ))=Measure.dirac (0:Fin k→ℝ):=by
  classical
  apply Measure.pi_eq
  intro s hs
  by_cases h:∀i:Fin k,(0:ℝ)∈s i
  · have hmem:(0:Fin k→ℝ)∈Set.pi Set.univ s:=by simpa only [Set.mem_pi,Set.mem_univ,Pi.zero_apply,forall_const] using h
    rw [Measure.dirac_apply_of_mem hmem]
    symm
    apply Finset.prod_eq_one
    intro i hi
    exact Measure.dirac_apply_of_mem (h i)
  · have hnot:(0:Fin k→ℝ)∉Set.pi Set.univ s:=by simpa only [Set.mem_pi,Set.mem_univ,Pi.zero_apply,forall_const] using h
    rw [Measure.dirac_apply,Set.indicator_of_notMem hnot]
    obtain ⟨i,hi⟩:=not_forall.mp h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Measure.dirac_apply,hi])

lemma weightedTightCoefficient_dirac_zero {P:PsiTheory} {G:WeilPeterssonGeometry P}
    (T:TightRegions G) (g p k:ℕ) (L:Fin p→ℝ):
    weightedTightCoefficient T g p k L (Measure.dirac (0:ℝ))=
      tightVolume T g p k L (fun _=>0)/(k.factorial:ℝ):=by
  rw [weightedTightCoefficient,pi_dirac_zero,integral_dirac]
  rfl

lemma geometric_tight_cusp_coefficient {P:PsiTheory} {G:WeilPeterssonGeometry P}
    (T:TightRegions G) (B:BuddZonneveldTransform G T)
    (g p:ℕ) (hs:Stable g p) (L:Fin p→ℝ) (hL:∀i,0≤L i) (k:ℕ):
    tightVolume T g p k L (fun _=>0)/
      ((2*Real.pi^2)^(dimension g p+k)*(k.factorial:ℝ))=
      realCoeff (momentTightG P g p L) k:=by
  have hc:(2*Real.pi^2:ℝ)≠0:=by positivity
  have hC:((2*Real.pi^2:ℝ):ℂ)≠0:=by exact_mod_cast hc
  have hfac:(k.factorial:ℝ)≠0:=by positivity
  have hweight:∃B:ℝ,0≤B ∧ Measure.dirac (0:ℝ) (Icc (0:ℝ) B)ᶜ=0:=by
    refine ⟨0,le_rfl,?_⟩
    simp
  have h:=B.weighted_taylor g p hs L hL (Measure.dirac (0:ℝ)) hweight
    (physicalCuspRoot P) (physicalCuspRoot_analyticAt P) (physicalCuspRoot_zero P)
    (physicalCuspRoot_root P) k
  rw [weightedTightCoefficient_dirac_zero] at h
  change tightVolume T g p k L (fun _=>0)/(k.factorial:ℝ)=
    realCoeff (fun t=>complexMomentPolynomial P g p
      (fun j=>classicalMomentGerm (Measure.dirac (0:ℝ)) (physicalCuspRoot P) j t) L) k at h
  have hf:(fun t:ℂ=>complexMomentPolynomial P g p
      (fun j=>classicalMomentGerm (Measure.dirac (0:ℝ)) (physicalCuspRoot P) j t) L)=
      (fun t:ℂ=>((2*Real.pi^2)^(dimension g p):ℝ)*momentTightG P g p L ((2*Real.pi^2:ℝ)*t)):=by
    funext t
    simp_rw [physicalCuspRoot_moments]
    unfold momentTightG
    rw [←Complex.ofReal_pow]
    rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ hc))]
  rw [hf,Analysis.realCoeff_const_mul,Analysis.realCoeff_comp_mul_left] at h
  rw [pow_add]
  apply (div_eq_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ hc)) hfac)).mpr
  rw [(div_eq_iff hfac).mp h]
  ring

end WP.TightMoments
