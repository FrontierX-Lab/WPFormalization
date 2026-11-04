import WPFormalization.Analysis.BorelArc
import Mathlib

/-! The actual difference of the two principal square-root banks cancels the
analytic local term. Finite sector deformation and a real affine substitution
then give the exact local-cut integral, with both joining arcs retained. -/
noncomputable section
namespace WP.Analysis
open Complex MeasureTheory Set Filter Metric
open scoped Interval

lemma firstCutBank_sub (H α β : ℂ → ℂ) (S : ℂ) (t : ℝ) :
    firstCutLowerBank H α β S t-firstCutUpperBank H α β S t=
      (Ioi (1:ℝ)).indicator (fun t:ℝ => (-2*Complex.I)*S*
        (Real.sqrt (t-1):ℂ)⁻¹*α (t:ℂ)) t := by
  by_cases hlt : t<1
  · have ht : t∉Ioi (1:ℝ) := by simpa only [mem_Ioi,not_lt] using hlt.le
    simp [firstCutLowerBank,firstCutUpperBank,hlt,Set.indicator_of_notMem ht]
  · by_cases ht1 : t=1
    · subst t
      simp [firstCutLowerBank,firstCutUpperBank]
    · have hgt : t∈Ioi (1:ℝ) := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm ht1)
      rw [firstCutLowerBank,firstCutUpperBank,ite_eq_right hlt,ite_eq_right hlt,
        Set.indicator_of_mem hgt]
      simp only [mul_inv_rev,inv_neg,Complex.inv_I,neg_neg]
      ring

lemma firstCutBank_weighted_integral_sub (H α β : ℂ → ℂ) (S : ℂ) (r ξ : ℝ)
    (hr : 0≤r)
    (hLo : IntegrableOn (fun t:ℝ => Complex.exp (-(ξ:ℂ)*(t:ℂ))*firstCutLowerBank H α β S t) (Ioc 0 (1+r)))
    (hUp : IntegrableOn (fun t:ℝ => Complex.exp (-(ξ:ℂ)*(t:ℂ))*firstCutUpperBank H α β S t) (Ioc 0 (1+r))) :
    (∫ t in Ioc 0 (1+r),Complex.exp (-(ξ:ℂ)*(t:ℂ))*firstCutLowerBank H α β S t)-
      (∫ t in Ioc 0 (1+r),Complex.exp (-(ξ:ℂ)*(t:ℂ))*firstCutUpperBank H α β S t)=
      ((-2*Complex.I)*S)*(∫ t in (1:ℝ)..(1+r),Complex.exp (-(ξ:ℂ)*(t:ℂ))*
        (Real.sqrt (t-1):ℂ)⁻¹*α (t:ℂ)) := by
  rw [←integral_sub hLo hUp]
  have he : (fun t:ℝ => Complex.exp (-(ξ:ℂ)*(t:ℂ))*firstCutLowerBank H α β S t-
      Complex.exp (-(ξ:ℂ)*(t:ℂ))*firstCutUpperBank H α β S t)=
      (Ioi (1:ℝ)).indicator (fun t:ℝ => ((-2*Complex.I)*S)*
        (Complex.exp (-(ξ:ℂ)*(t:ℂ))*(Real.sqrt (t-1):ℂ)⁻¹*α (t:ℂ))) := by
    funext t
    rw [←mul_sub,firstCutBank_sub]
    by_cases ht : t∈Ioi (1:ℝ)
    · rw [Set.indicator_of_mem ht,Set.indicator_of_mem ht]
      ring
    · rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem ht,mul_zero]
  rw [he,setIntegral_indicator measurableSet_Ioi]
  have hset : Ioc (0:ℝ) (1+r)∩Ioi 1=Ioc 1 (1+r) := by
    ext t
    simp only [mem_inter_iff,mem_Ioc,mem_Ioi]
    constructor
    · rintro ⟨ht,ht1⟩
      exact ⟨ht1,ht.2⟩
    · rintro ⟨ht,ht1⟩
      exact ⟨⟨by linarith,ht1⟩,ht⟩
  rw [hset,integral_const_mul,intervalIntegral.integral_of_le (by linarith : (1:ℝ)≤1+r)]

lemma local_sqrt_cut_integral_shift (α : ℂ → ℂ) (r ξ : ℝ) :
    (∫ t in (1:ℝ)..(1+r),Complex.exp (-(ξ:ℂ)*(t:ℂ))*
      (Real.sqrt (t-1):ℂ)⁻¹*α (t:ℂ))=
      Complex.exp (-(ξ:ℂ))*(∫ v in (0:ℝ)..r,Complex.exp (-(ξ:ℂ)*(v:ℂ))*
        (Real.sqrt v:ℂ)⁻¹*α (1+(v:ℂ))) := by
  let f : ℝ → ℂ := fun t => Complex.exp (-(ξ:ℂ)*(t:ℂ))*(Real.sqrt (t-1):ℂ)⁻¹*α (t:ℂ)
  have hs := intervalIntegral.integral_comp_add_right f (a:=0) (b:=r) (1:ℝ)
  simp only [zero_add] at hs
  rw [show (1:ℝ)+r=r+1 by ring,←hs,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  dsimp only [f]
  rw [show v+1-1=v by ring]
  have ha : ((v+1:ℝ):ℂ)=1+(v:ℂ) := by push_cast;ring
  rw [ha]
  have he : -(ξ:ℂ)*(1+(v:ℂ))=-(ξ:ℂ)+(-(ξ:ℂ)*(v:ℂ)) := by ring
  rw [he,Complex.exp_add]
  ring
lemma firstCutBanks_weighted_integrable (H α β : ℂ → ℂ) (S : ℂ) (r ξ : ℝ)
    (hr : 0<r) (hξ : 0≤ξ)
    (hH : AnalyticOnNhd ℂ H firstBorelSlit)
    (hα : AnalyticOnNhd ℂ α (closedBall 1 (2*r)))
    (hβ : AnalyticOnNhd ℂ β (closedBall 1 (2*r)))
    (hform : ∀z:ℂ,‖z-1‖ < 2*r → z.im≠0 →
      H z=S*(Complex.sqrt (1-z))⁻¹*α z+β z) :
    IntegrableOn (fun t:ℝ => Complex.exp (-(ξ:ℂ)*(t:ℂ))*firstCutLowerBank H α β S t) (Ioc 0 (1+r)) ∧
      IntegrableOn (fun t:ℝ => Complex.exp (-(ξ:ℂ)*(t:ℂ))*firstCutUpperBank H α β S t) (Ioc 0 (1+r)) := by
  constructor
  · let l := nhdsWithin (0:ℝ) (Iio 0)
    have hl : Tendsto (fun θ:ℝ => θ) l (nhds 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hs : ∀ᶠ θ in l,Real.sin θ≠0 := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds (show -Real.pi<(0:ℝ) by linarith [Real.pi_pos])).filter_mono nhdsWithin_le_nhds]
        with θ hθ hθπ
      exact (Real.sin_neg_of_neg_of_neg_pi_lt hθ hθπ).ne
    exact (radial_laplace_bank_integral_limit H α β S r ξ hr hξ hH hα hβ hform l hl hs
      (firstCutLowerBank H α β S)
      (fun t ht ht1 => radial_H_lower_bank_limit H α β S r t hr ht ht1 hH hα hβ hform)).1
  · let l := nhdsWithin (0:ℝ) (Ioi 0)
    have hl : Tendsto (fun θ:ℝ => θ) l (nhds 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hs : ∀ᶠ θ in l,Real.sin θ≠0 := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds Real.pi_pos).filter_mono nhdsWithin_le_nhds] with θ hθ hθπ
      exact (Real.sin_pos_of_pos_of_lt_pi hθ hθπ).ne'
    exact (radial_laplace_bank_integral_limit H α β S r ξ hr hξ hH hα hβ hform l hl hs
      (firstCutUpperBank H α β S)
      (fun t ht ht1 => radial_H_upper_bank_limit H α β S r t hr ht ht1 hH hα hβ hform)).1

lemma finite_slit_local_cut_identity (H α β : ℂ → ℂ) (S : ℂ) (r ξ φ : ℝ)
    (hr : 0<r) (hξ : 0≤ξ) (hφ : 0<φ) (hφπ : φ<Real.pi/2)
    (hφdist : ∀θ∈Icc (-φ) φ,‖Complex.exp ((θ:ℂ)*Complex.I)-1‖≤r/(2*(1+r)))
    (hH : AnalyticOnNhd ℂ H firstBorelSlit)
    (hα : AnalyticOnNhd ℂ α (closedBall 1 (2*r)))
    (hβ : AnalyticOnNhd ℂ β (closedBall 1 (2*r)))
    (hform : ∀z:ℂ,‖z-1‖ < 2*r → z.im≠0 →
      H z=S*(Complex.sqrt (1-z))⁻¹*α z+β z) :
    radialSegmentIntegral (laplaceSlitFunction H ξ) (-φ) 0 (1+r)-
      radialSegmentIntegral (laplaceSlitFunction H ξ) φ 0 (1+r)=
      ((-2*Complex.I)*S)*Complex.exp (-(ξ:ℂ))*
        (∫ v in (0:ℝ)..r,Complex.exp (-(ξ:ℂ)*(v:ℂ))*
          (Real.sqrt v:ℂ)⁻¹*α (1+(v:ℂ)))-
      polarArcIntegral (laplaceSlitFunction H ξ) (1+r) (-φ) 0-
      polarArcIntegral (laplaceSlitFunction H ξ) (1+r) 0 φ := by
  have hUp := finite_slit_upper_bank_identity H α β S r ξ φ hr hξ hφ hφπ hφdist hH hα hβ hform
  have hLo := finite_slit_lower_bank_identity H α β S r ξ φ hr hξ hφ hφπ hφdist hH hα hβ hform
  obtain ⟨hLoI,hUpI⟩ := firstCutBanks_weighted_integrable H α β S r ξ hr hξ hH hα hβ hform
  have hDiff := firstCutBank_weighted_integral_sub H α β S r ξ hr.le hLoI hUpI
  rw [local_sqrt_cut_integral_shift α r ξ] at hDiff
  rw [hUp,hLo]
  linear_combination hDiff

end WP.Analysis
