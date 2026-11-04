import WPFormalization.Analysis.Taylor
import Mathlib.Analysis.Complex.Liouville
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma coeff_eq_circleIntegral (f:ℂ→ℂ)(R:ℝ)(hR:0<R)
    (hf:DifferentiableOn ℂ f (Metric.closedBall 0 R))(n:ℕ) :
    WP.coeff f n = (2*Real.pi*Complex.I)⁻¹ * ∮ z in C(0,R), (1/z^(n+1))*f z := by
  have h := hf.circleIntegral_one_div_sub_center_pow_smul hR n
  simp only [sub_zero,smul_eq_mul] at h
  rw [h]
  unfold WP.coeff
  have hp : (2*Real.pi*Complex.I)≠0 := by simp [Real.pi_ne_zero]
  field_simp
lemma parameter_coeff_continuous {P:Type*}[TopologicalSpace P][FirstCountableTopology P][LocallyCompactSpace P]
    (F:P→ℂ→ℂ)(R:ℝ)(hR:0<R)
    (hDiff:∀p,DifferentiableOn ℂ (F p) (Metric.closedBall 0 R))
    (hF:Continuous (fun p:P×Metric.closedBall (0:ℂ) R => F p.1 p.2)) (n:ℕ) :
    Continuous (fun p=>WP.coeff (F p) n) := by
  let q (p:P)(θ:ℝ) : ℂ := deriv (circleMap 0 R) θ *((1/(circleMap 0 R θ)^(n+1))*F p (circleMap 0 R θ))
  have hq : Continuous (fun p:P×ℝ=>q p.1 p.2) := by
    have hm : Continuous (fun p:P×ℝ=>circleMap 0 R p.2) := (continuous_circleMap 0 R).comp continuous_snd
    have hmi : Continuous (fun p:P×ℝ=>(circleMap 0 R p.2)⁻¹) := hm.inv₀ (fun p=>circleMap_ne_center (ne_of_gt hR))
    have hmap : Continuous (fun p:P×ℝ=>(p.1,(⟨circleMap 0 R p.2,circleMap_mem_closedBall 0 hR.le p.2⟩:Metric.closedBall (0:ℂ) R))) :=
      continuous_fst.prodMk (hm.subtype_mk _)
    have hf : Continuous (fun p:P×ℝ=>F p.1 (circleMap 0 R p.2)) := hF.comp hmap
    have hd : Continuous (fun p:P×ℝ=>deriv (circleMap 0 R) p.2) := by simp only [deriv_circleMap]; fun_prop
    dsimp [q]
    have hp : Continuous (fun p:P×ℝ=>deriv (circleMap 0 R) p.2*((circleMap 0 R p.2)⁻¹^(n+1)*F p.1 (circleMap 0 R p.2))) := hd.mul ((hmi.pow (n+1)).mul hf)
    simpa only [one_div,inv_pow] using hp
  have hi := continuous_parametric_integral_of_continuous (X := P) (Y := ℝ) (E := ℂ)
    (f := q) (μ := volume) hq (s := Icc (0:ℝ) (2*Real.pi)) isCompact_Icc
  have hi' : Continuous (fun p=>∫ θ:ℝ in (0)..(2*Real.pi), q p θ) := by
    convert hi using 1
    ext p
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi)]
  have he : (fun p=>WP.coeff (F p) n) = fun p=>(2*Real.pi*Complex.I)⁻¹*(∫ θ:ℝ in (0)..(2*Real.pi),q p θ) := by
    funext p
    exact coeff_eq_circleIntegral (F p) R hR (hDiff p) n
  rw [he]
  exact continuous_const.mul hi'
lemma entire_ofReal_im_zero_of_realCoefficients (f:ℂ→ℂ)(hf:Differentiable ℂ f)
    (hr:RealCoefficients f)(x:ℝ) : (f x).im=0 := by
  have hs : HasSum (fun n=>WP.coeff f n*(x:ℂ)^n) (f x) := by
    convert Complex.hasSum_taylorSeries_of_entire hf 0 (x:ℂ) using 1
    ext n
    simp only [WP.coeff,sub_zero,smul_eq_mul]
    ring
  have hz : HasSum (fun n=>(WP.coeff f n*(x:ℂ)^n).im) 0 := by
    have he : (fun n=>(WP.coeff f n*(x:ℂ)^n).im) = (fun _ : ℕ => (0:ℝ)) := by
      ext n
      rw [Complex.mul_im,hr n]
      simp only [←Complex.ofReal_pow,Complex.ofReal_im,mul_zero,zero_mul,add_zero]
    rw [he]
    exact hasSum_zero
  exact (Complex.hasSum_im hs).unique hz
end WP.Analysis
