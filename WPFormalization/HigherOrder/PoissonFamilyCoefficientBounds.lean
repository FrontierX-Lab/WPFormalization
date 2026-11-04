import WPFormalization.HigherOrder.PoissonFamilyCoefficients
import WPFormalization.Analysis.PoissonFiniteAlgebra
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma poissonFamilyCoefficient_uniform_bounds (f:ℕ→ℂ × ℂ → ℂ) (R A B:ℝ)
    (hR:0<R) (hA:0<A) (hB:0<B)
    (hfa:∀s,AnalyticOnNhd ℂ (f s) (Metric.ball 0 R))
    (hfb:∀s v,v∈Metric.ball (0:ℂ × ℂ) R→‖f s v‖≤A*B^s*(s.factorial:ℝ)^2):
    ∃ν₀ C D:ℝ,0<ν₀∧ν₀<R∧0<C∧0<D∧∀n,
      AnalyticOnNhd ℂ (poissonFamilyCoefficient f n) (Metric.ball 0 ν₀)∧
      ∀ν:ℂ,‖ν‖<ν₀→‖poissonFamilyCoefficient f n ν‖≤C*D^n*(n.factorial:ℝ)^2:=by
  obtain ⟨ν₀,E,hν₀,hνR,hE,hall⟩:=poisson_central_expansion_uniform_homogeneous R hR
  have hs(s:ℕ):=(hall (f s) (A*B^s*(s.factorial:ℝ)^2) (by positivity) (hfa s) (hfb s))
  refine ⟨ν₀,2*A*E,2*max B E,hν₀,hνR,by positivity,by positivity,?_⟩
  intro n
  refine ⟨poissonFamilyCoefficient_analyticOnNhd f _ (fun s i=>(hs s).2.1 i) n,?_⟩
  intro ν hν
  exact Analysis.poisson_diagonal_convolution_bound (fun s i=>poissonCentralAmplitude (f s) i ν)
    A B E hA hB hE (fun s i=> (hs s).2.2.1 i ν hν) n
def normalizedPoissonFamilyCoefficient (f:ℕ→ℂ × ℂ → ℂ) (n:ℕ) (ν:ℂ):ℂ:=
  poissonFamilyCoefficient f n ν/poissonFamilyCoefficient f 0 ν
lemma normalizedPoissonFamilyCoefficient_at_zero (f:ℕ→ℂ × ℂ → ℂ) (hf:f 0 (0,0)=1) (n:ℕ):
    normalizedPoissonFamilyCoefficient f n 0=f n (0,0):=by
  simp only[normalizedPoissonFamilyCoefficient,poissonFamilyCoefficient_at_zero,hf,div_one]
lemma normalizedPoissonFamilyCoefficient_uniform_bounds (f:ℕ→ℂ × ℂ → ℂ) (R A B:ℝ)
    (hR:0<R) (hA:0<A) (hB:0<B)
    (hfa:∀s,AnalyticOnNhd ℂ (f s) (Metric.ball 0 R))
    (hfb:∀s v,v∈Metric.ball (0:ℂ × ℂ) R→‖f s v‖≤A*B^s*(s.factorial:ℝ)^2)
    (hf0:f 0 (0,0)=1):
    ∃ν₀ C D:ℝ,0<ν₀∧ν₀<R∧0<C∧0<D∧
      (∀ν:ℂ,‖ν‖<ν₀→1/2≤‖poissonFamilyCoefficient f 0 ν‖)∧
      ∀n,AnalyticOnNhd ℂ (normalizedPoissonFamilyCoefficient f n) (Metric.ball 0 ν₀)∧
        ∀ν:ℂ,‖ν‖<ν₀→‖normalizedPoissonFamilyCoefficient f n ν‖≤C*D^n*(n.factorial:ℝ)^2:=by
  obtain ⟨ν,C,D,hν,hνR,hC,hD,hcoef⟩:=poissonFamilyCoefficient_uniform_bounds f R A B hR hA hB hfa hfb
  have h0:poissonFamilyCoefficient f 0 0=1:=by rw[poissonFamilyCoefficient_at_zero,hf0]
  have h0a:AnalyticAt ℂ (poissonFamilyCoefficient f 0) 0:=(hcoef 0).1 0 (Metric.mem_ball_self hν)
  have hnorm:∀ᶠz:ℂ in 𝓝 0,(1/2:ℝ)<‖poissonFamilyCoefficient f 0 z‖:=
    h0a.continuousAt.norm.tendsto.eventually (eventually_gt_nhds (by rw[h0,norm_one];norm_num))
  obtain ⟨r,hr,hrball⟩:=Metric.eventually_nhds_iff.mp hnorm
  let ν₀:ℝ:=min ν r
  have hν₀:0<ν₀:=lt_min hν hr
  have hlocal(z:ℂ) (hz:‖z‖<ν₀):(1/2:ℝ)≤‖poissonFamilyCoefficient f 0 z‖:=
    (hrball (by simpa only[dist_zero_right] using hz.trans_le (min_le_right ν r))).le
  refine ⟨ν₀,2*C,D,hν₀,(min_le_left _ _).trans_lt hνR,by positivity,hD,hlocal,?_⟩
  intro n
  constructor
  · intro z hz
    have hn:‖z‖<ν₀:=by simpa only[Metric.mem_ball,dist_zero_right] using hz
    have hzν:‖z‖<ν:=hn.trans_le (min_le_left ν r)
    have hzn:poissonFamilyCoefficient f 0 z≠0:=by
      apply norm_ne_zero_iff.mp
      exact ne_of_gt (lt_of_lt_of_le (by norm_num:0<(1/2:ℝ)) (hlocal z hn))
    exact ((hcoef n).1 z (by simpa only[Metric.mem_ball,dist_zero_right] using hzν)).div
      ((hcoef 0).1 z (by simpa only[Metric.mem_ball,dist_zero_right] using hzν)) hzn
  · intro z hz
    rw[normalizedPoissonFamilyCoefficient,norm_div]
    have hden:0<‖poissonFamilyCoefficient f 0 z‖:=lt_of_lt_of_le (by norm_num:0<(1/2:ℝ)) (hlocal z hz)
    apply (div_le_iff₀ hden).mpr
    have hnum:‖poissonFamilyCoefficient f n z‖≤C*D^n*(n.factorial:ℝ)^2:=
      (hcoef n).2 z (hz.trans_le (min_le_left ν r))
    have hd:=mul_le_mul_of_nonneg_left (hlocal z hz)
      (by positivity:0≤(2*C)*D^n*(n.factorial:ℝ)^2)
    nlinarith
end WP.HigherOrder
