import WPFormalization.Analysis.GaussianContour
/-! Exact finite Morse substitution and genuine Gaussian endpoint connector errors. All hypotheses describe explicit analytic functions and finite paths; the proof uses the existing primitive/Cauchy theorem and no asymptotic assumption. -/
noncomputable section
open Set MeasureTheory
namespace WP.Analysis
lemma fixed_morse_integral_connector_bound (φ a U b:ℂ→ℂ) (h M r R S:ℝ) (ep en:ℂ)
    (hh:0<h) (hM:0≤M) (hr:0<r) (hrR:r<R) (hrS:r<S)
    (hφ:DifferentiableOn ℂ φ (Metric.ball 0 S)) (ha:DifferentiableOn ℂ a (Metric.ball 0 S))
    (hU:DifferentiableOn ℂ U (Metric.ball 0 R))
    (hmap:MapsTo U (Metric.ball 0 R) (Metric.ball 0 S))
    (hjet:∀z∈Metric.ball (0:ℂ) R,φ (U z)=-z^2/2 ∧ a (U z)*deriv U z=b z)
    (hb:∀z∈Metric.ball (0:ℂ) R,‖b z‖≤M)
    (hep:‖ep‖≤r/4) (hen:‖en‖≤r/4)
    (hp:‖(r:ℂ)+ep‖<R) (hn:‖-(r:ℂ)+en‖<R)
    (hUp:U ((r:ℂ)+ep)=(r:ℂ)) (hUn:U (-(r:ℂ)+en)= -(r:ℂ)) :
    ‖(∫u:ℝ in (-r)..r,Complex.exp ((h:ℂ)*φ (u:ℂ))*a (u:ℂ))-
      (∫w:ℝ in (-r)..r,Complex.exp (-(h:ℂ)/2*(w:ℂ)^2)*b (w:ℂ))‖≤
      M*Real.exp (-(h/4)*r^2)*(‖ep‖+‖en‖) := by
  let f:ℂ→ℂ:=fun z=>Complex.exp ((h:ℂ)*φ z)*a z
  let g:ℂ→ℂ:=fun z=>f (U z)*deriv U z
  let G:ℂ→ℂ:=fun z=>Complex.exp (-(h:ℂ)/2*z^2)*b z
  have hf:DifferentiableOn ℂ f (Metric.ball 0 S):=by
    intro z hz
    exact (((hφ z hz).const_mul (h:ℂ)).cexp).mul (ha z hz)
  have hgreal(z:ℂ)(hz:z∈Metric.ball (0:ℂ) R):g z=G z := by
    dsimp only[g,G,f]
    rw[(hjet z hz).1,mul_assoc,(hjet z hz).2]
    congr 2
    ring
  have hreal(w:ℝ)(hw:w∈Icc (-r) r):(w:ℂ)∈Metric.ball (0:ℂ) R := by
    rw[Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith[hw.1],hw.2⟩).trans_lt hrR
  have hi:(∫w:ℝ in (-r)..r,g (w:ℂ))=∫w:ℝ in (-r)..r,G (w:ℂ) := by
    apply intervalIntegral.integral_congr
    intro w hw
    exact hgreal _ (hreal w (by simpa only[uIcc_of_le (by linarith:-r≤r)] using hw))
  have hs(c d:ℂ)(hc:‖c‖<R)(hd:‖d‖<R):complexSegmentIntegral g c d=complexSegmentIntegral G c d := by
    unfold complexSegmentIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    have htI:t∈Icc (0:ℝ) 1:=by simpa only[uIcc_of_le (show (0:ℝ)≤1 by norm_num)] using ht
    change g (c+(t:ℂ)*(d-c))*(d-c)=G (c+(t:ℂ)*(d-c))*(d-c)
    congr 1
    apply hgreal
    have hcv:= (convex_ball (0:ℂ) R).add_smul_sub_mem
      (show c∈Metric.ball (0:ℂ) R by simpa only[Metric.mem_ball,dist_zero_right] using hc)
      (show d∈Metric.ball (0:ℂ) R by simpa only[Metric.mem_ball,dist_zero_right] using hd) htI
    simpa only[Complex.real_smul] using hcv
  have hpos:‖(r:ℂ)‖<R:=by rw[Complex.norm_of_nonneg hr.le];exact hrR
  have hneg:‖-(r:ℂ)‖<R:=by rw[norm_neg];exact hpos
  have he:=finite_analytic_substitution_contour f U r R S (-(r:ℂ)+en) ((r:ℂ)+ep)
    hr hrR hrS hf hU hmap hn hp hUn hUp
  change (∫u:ℝ in (-r)..r,f (u:ℂ))-(∫w:ℝ in (-r)..r,g (w:ℂ))=
    complexSegmentIntegral g (r:ℂ) ((r:ℂ)+ep)-complexSegmentIntegral g (-(r:ℂ)) (-(r:ℂ)+en) at he
  rw[hi,hs _ _ hpos hp,hs _ _ hneg hn] at he
  have hseg(z e:ℂ)(hz:‖z‖<R)(he:‖z+e‖<R):∀t∈Icc (0:ℝ) 1,‖b (z+(t:ℂ)*e)‖≤M := by
    intro t ht
    apply hb
    have hcv:Convex ℝ (Metric.ball (0:ℂ) R):=convex_ball _ _
    have hh:=hcv.add_smul_sub_mem
      (show z∈Metric.ball (0:ℂ) R by simpa only[Metric.mem_ball,dist_zero_right] using hz)
      (show z+e∈Metric.ball (0:ℂ) R by simpa only[Metric.mem_ball,dist_zero_right] using he) ht
    simpa only[add_sub_cancel_left,Complex.real_smul] using hh
  have hbp:=gaussian_connector_norm_bound b h M hh hM r ep (by simpa only[abs_of_pos hr] using hep)
    (hseg (r:ℂ) ep hpos hp)
  have hbn:=gaussian_connector_norm_bound b h M hh hM (-r) en (by simpa only[abs_neg,abs_of_pos hr] using hen)
    (by simpa only[Complex.ofReal_neg] using hseg (-(r:ℂ)) en hneg hn)
  rw[neg_sq] at hbn
  change ‖(∫u:ℝ in (-r)..r,f (u:ℂ))-(∫w:ℝ in (-r)..r,G (w:ℂ))‖≤_
  rw[he]
  exact (norm_sub_le _ _).trans ((add_le_add hbp (by simpa only[Complex.ofReal_neg] using hbn)).trans_eq (by ring))
end WP.Analysis
