import WPFormalization.Volumes.PositiveConvolutionAnalytic
import WPFormalization.Analysis.BesselSignBounds

/-! The entire positive translation kernels of the genuine boundary insertion.
The a-sum in Eq.9.26 is represented by an actual derivative of X, with its
original factorial coefficients. -/
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter PositiveConvolution
open scoped Topology

def translationKernel (b : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ)^b * iteratedDeriv (b+1) X (-z)

lemma translationKernel_analyticAt (b : ℕ) (z : ℂ) :
    AnalyticAt ℂ (translationKernel b) z := by
  exact analyticAt_const.mul (((iteratedDeriv_X_differentiable (b+1)).analyticAt _).comp
    analyticAt_id.neg)

lemma translationKernel_hasDerivAt (b : ℕ) (z : ℂ) :
    HasDerivAt (translationKernel b) (translationKernel (b+1) z) z := by
  have hd := (((iteratedDeriv_X_differentiable (b+1) (-z)).hasDerivAt).comp z
    (hasDerivAt_id z).neg).const_mul ((-1:ℂ)^b)
  convert hd using 1
  · rfl
  · dsimp only [translationKernel]
    rw [iteratedDeriv_succ,pow_succ]
    ring

lemma translationKernel_iteratedDeriv_zero (b n : ℕ) :
    iteratedDeriv n (translationKernel b) 0 = ((n+b).factorial : ℂ)⁻¹ := by
  change iteratedDeriv n (fun z : ℂ => (-1:ℂ)^b * iteratedDeriv (b+1) X (-z)) 0 = _
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_comp_neg,
    neg_zero,iteratedDeriv_iterated_X,iteratedDeriv_X_zero (n+(b+1)) (by omega)]
  have he : n+(b+1)-1=n+b := by omega
  simp only [smul_eq_mul,he]
  rw [← mul_assoc,← pow_add,← mul_div_assoc,← pow_add]
  have hp : (-1:ℂ)^(b+n+(n+b))=1 := by
    rw [show b+n+(n+b)=2*(n+b) by omega,pow_mul]
    norm_num
  rw [hp,one_div]

lemma translationKernel_positiveJets (b : ℕ) : PositiveJets (translationKernel b) := by
  intro n
  refine ⟨⟨((n+b).factorial:ℝ)⁻¹,by positivity⟩,?_⟩
  rw [translationKernel_iteratedDeriv_zero]
  change ((n+b).factorial:ℂ)⁻¹=Complex.ofReal (((n+b).factorial:ℝ)⁻¹)
  simp

lemma translationKernel_hasSum (b : ℕ) (z : ℂ) :
    HasSum (fun a : ℕ => z^a/((a.factorial:ℂ)*((a+b).factorial:ℂ)))
      (translationKernel b z) := by
  have hf : Differentiable ℂ (translationKernel b) :=
    fun z => (translationKernel_analyticAt b z).differentiableAt
  convert Complex.hasSum_taylorSeries_of_entire hf 0 z using 1
  ext a
  rw [translationKernel_iteratedDeriv_zero]
  simp only [sub_zero,smul_eq_mul]
  ring

lemma translationKernel_real_hasSum (b : ℕ) (Y : ℝ) :
    HasSum (fun a : ℕ => Y^a/((a.factorial:ℝ)*((a+b).factorial:ℝ)))
      ((translationKernel b (Y:ℂ)).re) := by
  have hs := (translationKernel_hasSum b (Y:ℂ)).mapL Complex.reCLM
  convert hs using 1
  · ext a
    simp only [←Complex.ofReal_natCast,←Complex.ofReal_mul,←Complex.ofReal_pow,
    ←Complex.ofReal_div,Complex.reCLM_apply,Complex.ofReal_re]
  · rfl

lemma translationKernel_ofReal (b : ℕ) (Y : ℝ) :
    translationKernel b (Y:ℂ)=Complex.ofReal ((translationKernel b (Y:ℂ)).re) := by
  have hs := (translationKernel_hasSum b (Y:ℂ)).mapL Complex.imCLM
  have hz : HasSum (fun _ : ℕ => (0:ℝ)) ((translationKernel b (Y:ℂ)).im) := by
    convert hs using 1
    · ext a
      simp only [←Complex.ofReal_natCast,←Complex.ofReal_mul,←Complex.ofReal_pow,
      ←Complex.ofReal_div,Complex.imCLM_apply,Complex.ofReal_im]
    · rfl
  apply Complex.ext
  · rfl
  · simpa using (hasSum_zero.unique hz).symm

lemma translationKernel_nonneg (b : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    0 ≤ (translationKernel b (Y:ℂ)).re := by
  exact (translationKernel_real_hasSum b Y).nonneg (fun a => by positivity)

/-- The length-dependent translation weight, before the odd factorial. -/
def translationWeight (t : ℝ) (b : ℕ) (z : ℂ) : ℂ :=
  (t:ℂ)^b * translationKernel b ((t:ℂ)*z)

lemma translationWeight_analyticAt (t : ℝ) (b : ℕ) (z : ℂ) :
    AnalyticAt ℂ (translationWeight t b) z := by
  exact analyticAt_const.mul ((translationKernel_analyticAt b _).comp
    (analyticAt_const.mul analyticAt_id))

lemma translationWeight_hasDerivAt (t : ℝ) (b : ℕ) (z : ℂ) :
    HasDerivAt (translationWeight t b) (translationWeight t (b+1) z) z := by
  have hd := ((translationKernel_hasDerivAt b ((t:ℂ)*z)).comp z
    ((hasDerivAt_id z).const_mul (t:ℂ))).const_mul ((t:ℂ)^b)
  convert hd using 1
  · rfl
  · dsimp only [translationWeight]
    rw [pow_succ]
    ring

lemma translationWeight_positiveJets (t : ℝ) (ht : 0 ≤ t) (b : ℕ) :
    PositiveJets (translationWeight t b) := by
  let c : NNReal := ⟨t,ht⟩
  have hlinear : PositiveJets (fun z : ℂ => (t:ℂ)*z) := by
    apply PositiveJets.mul analyticAt_const analyticAt_id
    · exact PositiveJets.const c
    · intro n
      refine ⟨if n=1 then 1 else 0,?_⟩
      change iteratedDeriv n id 0 = _
      simp only [iteratedDeriv_id]
      split_ifs <;> simp_all [nnComplexHom]
  have hc : PositiveJets (fun z : ℂ => translationKernel b ((t:ℂ)*z)) :=
    PositiveJets.comp (translationKernel_analyticAt b 0)
      (analyticAt_const.mul analyticAt_id) (by simp)
      (translationKernel_positiveJets b) hlinear
  have hlin : AnalyticAt ℂ (fun z : ℂ => (t:ℂ)*z) 0 :=
    analyticAt_const.mul analyticAt_id
  have hcomp : AnalyticAt ℂ (fun z : ℂ => translationKernel b ((t:ℂ)*z)) 0 :=
    (translationKernel_analyticAt b ((t:ℂ)*0)).comp hlin
  have hconst : PositiveJets (fun _ : ℂ => (t:ℂ)^b) := by
    convert PositiveJets.const (c^b) using 1
    funext z
    change (t:ℂ)^b = Complex.ofReal (((c^b):NNReal):ℝ)
    have hp : ((c^b:NNReal):ℝ) = t^b := map_pow NNReal.toRealHom c b
    rw [hp,Complex.ofReal_pow]
  exact PositiveJets.mul analyticAt_const hcomp hconst hc

end WP.BoundaryConvolution
