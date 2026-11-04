import WPFormalization.Volumes.PositiveConvolutionAnalytic
noncomputable section
set_option maxHeartbeats 1500000
namespace WP.PositiveConvolution
open Set Filter
open scoped Topology
lemma deriv_planarInverse_eq (P:PsiTheory):deriv (planarInverse P)=universalV P:=by
  funext z
  change deriv (iteratedDeriv 2 (Phi P 0)) z=iteratedDeriv 3 (Phi P 0) z
  simp only[iteratedDeriv_succ,iteratedDeriv_zero]
lemma universalV_deriv_zero (P:PsiTheory):deriv (universalV P) 0=1:=by
  have hz:‖(0:ℂ)‖<xCritical:=by simpa only[norm_zero] using Analysis.xCritical_pos_parameter
  have hy:HasDerivAt (planarInverse P) 1 0:=by
    have hh:=(planarInverse_analyticAt P 0 hz).differentiableAt.hasDerivAt
    rwa[deriv_planarInverse_eq,universalV_zero] at hh
  have hX:HasDerivAt (deriv X) (-1) (0:ℂ):=by
    have hh:=((X_differentiable.analyticAt 0).deriv).differentiableAt.hasDerivAt
    have he:deriv (deriv X) 0=(-1:ℂ):=by
      have hf:=iteratedDeriv_X_zero 2 (by omega)
      simpa only[iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero,Nat.reduceSub,Nat.factorial_one,Nat.cast_one,pow_one,div_one] using hf
    rwa[he] at hh
  have hA:=((by simpa only[planarInverse_zero] using hX):HasDerivAt (deriv X) (-1) (planarInverse P 0)).comp 0 hy
  have hV:HasDerivAt (universalV P) (deriv (universalV P) 0) 0:=by
    apply DifferentiableAt.hasDerivAt
    change DifferentiableAt ℂ (iteratedDeriv 3 (Phi P 0)) 0
    have hh:AnalyticAt ℂ (iteratedDeriv 3 (Phi P 0)) 0:=by
      simpa only[iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P 0 0 hz).iterated_deriv 3
    exact hh.differentiableAt
  have hp:=hA.mul hV
  have he:(fun z=>deriv X (planarInverse P z)*universalV P z)=ᶠ[𝓝 (0:ℂ)] (fun _:ℂ=>1):=by
    filter_upwards[Metric.ball_mem_nhds (0:ℂ) Analysis.xCritical_pos_parameter] with z hz'
    exact planar_inverse_derivative_identity P z (by simpa only[Metric.mem_ball,dist_zero_right] using hz')
  have hd:=he.deriv_eq
  have hp':deriv (fun z=>deriv X (planarInverse P z)*universalV P z) 0=
      -1+deriv (universalV P) 0:=by
    simpa only[Function.comp_def,Pi.mul_def,planarInverse_zero,Analysis.derivX_zero,universalV_zero,mul_one,one_mul,neg_mul] using hp.deriv
  rw[hp',deriv_const] at hd
  linear_combination hd
lemma planarInverse_first_coefficient (P:PsiTheory):WP.coeff (planarInverse P) 1=1:=by
  simp only[WP.coeff,iteratedDeriv_one,Nat.factorial_one,Nat.cast_one,div_one,
    deriv_planarInverse_eq,universalV_zero]
lemma planarInverse_second_coefficient (P:PsiTheory):WP.coeff (planarInverse P) 2=(1/2:ℂ):=by
  rw[WP.coeff,iteratedDeriv_succ,iteratedDeriv_one,deriv_planarInverse_eq,universalV_deriv_zero]
  norm_num
end WP.PositiveConvolution

namespace WP.PositiveConvolution
open Set Filter
open scoped Topology
lemma nonnegative_series_summable_at_endpoint (a:ℕ→ℝ) (ρ M:ℝ) (hρ:0<ρ)
    (ha:∀n,0 ≤ a n)
    (hbound:∀r:ℝ,0 ≤ r → r < ρ → ∀N:ℕ,∑n∈Finset.range N,a n*r^n ≤ M):
    Summable (fun n=>a n*ρ^n) ∧ (∑'n:ℕ,a n*ρ^n) ≤ M:=by
  have hN (N:ℕ):(∑n∈Finset.range N,a n*ρ^n) ≤ M:=by
    have hcont:Continuous (fun r:ℝ=>∑n∈Finset.range N,a n*r^n):=by fun_prop
    have ht:=hcont.continuousAt.tendsto.mono_left (show 𝓝[<] ρ ≤ 𝓝 ρ from nhdsWithin_le_nhds)
    apply le_of_tendsto ht
    filter_upwards[self_mem_nhdsWithin,
      (eventually_gt_nhds hρ).filter_mono (show 𝓝[<] ρ ≤ 𝓝 ρ from nhdsWithin_le_nhds)] with r hr hpos
    exact hbound r hpos.le hr N
  refine ⟨summable_of_sum_range_le (fun n=>mul_nonneg (ha n) (pow_nonneg hρ.le _)) hN,?_⟩
  exact Real.tsum_le_of_sum_range_le (fun n=>mul_nonneg (ha n) (pow_nonneg hρ.le _)) hN

def positiveSeriesSum (a:ℕ→ℝ) (z:ℂ):ℂ:=∑'n:ℕ,Complex.ofReal (a n)*z^n
lemma positiveSeriesSum_summable_closed (a:ℕ→ℝ) (ρ:ℝ) (ha:∀n,0 ≤ a n)
    (hs:Summable (fun n=>a n*ρ^n)) (z:ℂ) (hz:‖z‖ ≤ ρ):
    Summable (fun n=>Complex.ofReal (a n)*z^n):=by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n=>norm_nonneg _) _ hs
  intro n
  rw[norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha n),norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz _) (ha n)
lemma positiveSeriesSum_continuousOn_closed (a:ℕ→ℝ) (ρ:ℝ) (ha:∀n,0 ≤ a n)
    (hs:Summable (fun n=>a n*ρ^n)):
    ContinuousOn (positiveSeriesSum a) (Metric.closedBall (0:ℂ) ρ):=by
  apply continuousOn_tsum
  · intro n
    exact (by fun_prop:Continuous (fun z:ℂ=>Complex.ofReal (a n)*z^n)).continuousOn
  · exact hs
  · intro n z hz
    have hn:‖z‖ ≤ ρ:=by simpa only[Metric.mem_closedBall,dist_zero_right] using hz
    rw[norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha n),norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hn _) (ha n)
lemma planarInverse_scalar_hasSum (P:PsiTheory) (r:ℝ) (hr:0 ≤ r) (hrx:r<xCritical):
    HasSum (fun n=>realCoeff (planarInverse P) n*r^n) (inverseY r):=by
  have hn:‖(r:ℂ)‖<xCritical:=by simpa only[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr] using hrx
  have hs:=analytic_ball_hasSum (planarInverse P) xCritical Analysis.xCritical_pos_parameter
    (planarInverse_analyticAt P) (r:ℂ) hn
  have hR:=Complex.reCLM.hasSum hs
  have hvalue:(planarInverse P (r:ℂ)).re=inverseY r:=by rw[planarInverse_ofReal P r ⟨hr,hrx⟩];rfl
  change HasSum (fun n=>(WP.coeff (planarInverse P) n*(r:ℂ)^n).re)
    (planarInverse P (r:ℂ)).re at hR
  rw[hvalue] at hR
  convert hR using 1
  funext n
  rw[←Complex.ofReal_pow]
  simp only[Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,realCoeff]
lemma planarInverse_boundary_summable (P:PsiTheory):
    Summable (fun n=>realCoeff (planarInverse P) n*xCritical^n) ∧
      (∑'n:ℕ,realCoeff (planarInverse P) n*xCritical^n) ≤ y₀:=by
  have ha(n:ℕ):0 ≤ realCoeff (planarInverse P) n:=(planarInverse_positiveJets P).coefficient_nonneg n |>.1
  apply nonnegative_series_summable_at_endpoint _ xCritical y₀ Analysis.xCritical_pos_parameter ha
  intro r hr hrx N
  have hs:=planarInverse_scalar_hasSum P r hr hrx
  have hb:=(hs.summable.sum_le_tsum (Finset.range N) (fun n hn=>mul_nonneg (ha n) (pow_nonneg hr n)))
  rw[hs.tsum_eq] at hb
  exact hb.trans (inverseY_branch r ⟨hr,hrx⟩).1.2.le

def closedPlanarInverse (P:PsiTheory):ℂ→ℂ:=positiveSeriesSum (realCoeff (planarInverse P))
lemma closedPlanarInverse_continuousOn (P:PsiTheory):
    ContinuousOn (closedPlanarInverse P) (Metric.closedBall (0:ℂ) xCritical):=by
  exact positiveSeriesSum_continuousOn_closed _ _
    (fun n=>(planarInverse_positiveJets P).coefficient_nonneg n |>.1) (planarInverse_boundary_summable P).1
lemma closedPlanarInverse_eq_inside (P:PsiTheory) (z:ℂ) (hz:‖z‖<xCritical):
    closedPlanarInverse P z=planarInverse P z:=by
  have hs:=analytic_ball_hasSum (planarInverse P) xCritical Analysis.xCritical_pos_parameter
    (planarInverse_analyticAt P) z hz
  have hc(n:ℕ):WP.coeff (planarInverse P) n=Complex.ofReal (realCoeff (planarInverse P) n):=by
    apply Complex.ext
    · rfl
    · simpa only[Complex.ofReal_im] using (planarInverse_positiveJets P).coefficient_nonneg n |>.2
  simpa only[closedPlanarInverse,positiveSeriesSum,hc] using hs.tsum_eq
end WP.PositiveConvolution

namespace WP.PositiveConvolution
lemma norm_positive_linear_lt (a b ρ:ℝ) (ha:0<a) (hb:0<b) (hρ:0<ρ)
    (z:ℂ) (hz:‖z‖=ρ) (hre:z.re<ρ):
    ‖(a:ℂ)+(b:ℂ)*z‖<a+b*ρ:=by
  have hnorm:z.re^2+z.im^2=ρ^2:=by
    have he:=Complex.sq_norm z
    rw[hz,Complex.normSq_apply] at he
    nlinarith
  have hval:‖(a:ℂ)+(b:ℂ)*z‖^2=(a+b*z.re)^2+(b*z.im)^2:=by
    rw[Complex.sq_norm,Complex.normSq_apply]
    simp only[Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero,Complex.add_im,Complex.mul_im,zero_mul,zero_add]
    ring
  have heq:(a+b*ρ)^2-‖(a:ℂ)+(b:ℂ)*z‖^2=2*a*b*(ρ-z.re):=by
    rw[hval]
    nlinarith[congrArg (fun t:ℝ=>b^2*t) hnorm]
  have hpos:0<2*a*b*(ρ-z.re):=by positivity
  have hbound:0<a+b*ρ:=by positivity
  nlinarith[norm_nonneg ((a:ℂ)+(b:ℂ)*z)]
lemma norm_first_two_terms_lt (a b ρ:ℝ) (ha:0<a) (hb:0<b) (hρ:0<ρ)
    (z:ℂ) (hz:‖z‖=ρ) (hre:z.re<ρ):
    ‖(a:ℂ)*z+(b:ℂ)*z^2‖<a*ρ+b*ρ^2:=by
  have he:(a:ℂ)*z+(b:ℂ)*z^2=z*((a:ℂ)+(b:ℂ)*z):=by ring
  rw[he,norm_mul,hz]
  convert mul_lt_mul_of_pos_left (norm_positive_linear_lt a b ρ ha hb hρ z hz hre) hρ using 1 <;>ring
lemma re_lt_norm_of_ne_positive (ρ:ℝ) (z:ℂ) (hz:‖z‖=ρ) (hne:z≠Complex.ofReal ρ):z.re<ρ:=by
  have hle:z.re ≤ ρ:=by simpa only[hz] using Complex.re_le_norm z
  by_contra hn
  have he:z.re=ρ:=by linarith
  have him:z.im=0:=by
    have hsq:=Complex.sq_norm z
    rw[hz,Complex.normSq_apply,he] at hsq
    nlinarith
  apply hne
  apply Complex.ext
  · simpa only[Complex.ofReal_re] using he
  · simpa only[Complex.ofReal_im] using him
end WP.PositiveConvolution

namespace WP.PositiveConvolution
lemma positiveSeriesSum_boundary_norm_lt (a:ℕ→ℝ) (ρ:ℝ) (ha:∀n,0≤a n)
    (hρ:0<ρ) (hs:Summable (fun n=>a n*ρ^n)) (ha0:a 0=0)
    (ha1:0<a 1) (ha2:0<a 2) (z:ℂ) (hz:‖z‖=ρ) (hne:z≠Complex.ofReal ρ):
    ‖positiveSeriesSum a z‖ < ∑'n:ℕ,a n*ρ^n:=by
  have hc:=positiveSeriesSum_summable_closed a ρ ha hs z hz.le
  have hn(n:ℕ):‖Complex.ofReal (a n)*z^n‖=a n*ρ^n:=by
    rw[norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha n),norm_pow,hz]
  have htC:Summable (fun n:ℕ=>Complex.ofReal (a (n+3))*z^(n+3)):=
    (summable_nat_add_iff 3).mpr hc
  have htR:Summable (fun n:ℕ=>a (n+3)*ρ^(n+3)):=
    (summable_nat_add_iff 3).mpr hs
  have htail:‖∑'n:ℕ,Complex.ofReal (a (n+3))*z^(n+3)‖≤∑'n:ℕ,a (n+3)*ρ^(n+3):=by
    exact htC.hasSum.norm_le_of_bounded htR.hasSum (fun n=>le_of_eq (hn (n+3)))
  have hp:=norm_first_two_terms_lt (a 1) (a 2) ρ ha1 ha2 hρ z hz
    (re_lt_norm_of_ne_positive ρ z hz hne)
  have heC:=hc.sum_add_tsum_nat_add 3
  have heR:=hs.sum_add_tsum_nat_add 3
  have hpC:(∑n∈Finset.range 3,Complex.ofReal (a n)*z^n)=
      Complex.ofReal (a 1)*z+Complex.ofReal (a 2)*z^2:=by
    simp[Finset.sum_range_succ,ha0]
  have hpR:(∑n∈Finset.range 3,a n*ρ^n)=a 1*ρ+a 2*ρ^2:=by
    simp[Finset.sum_range_succ,ha0]
  rw[hpC] at heC
  rw[hpR] at heR
  change ‖∑'n:ℕ,Complex.ofReal (a n)*z^n‖ < _
  rw[←heC,←heR]
  exact lt_of_le_of_lt (norm_add_le _ _) (add_lt_add_of_lt_of_le hp htail)
lemma closedPlanarInverse_strict_boundary (P:PsiTheory) (z:ℂ)
    (hz:‖z‖=xCritical) (hne:z≠Complex.ofReal xCritical):
    ‖closedPlanarInverse P z‖<y₀:=by
  have ha(n:ℕ):0≤realCoeff (planarInverse P) n:=
    (planarInverse_positiveJets P).coefficient_nonneg n |>.1
  have ha0:realCoeff (planarInverse P) 0=0:=by
    simp[realCoeff,WP.coeff,planarInverse_zero]
  have ha1:0<realCoeff (planarInverse P) 1:=by
    simp[realCoeff,planarInverse_first_coefficient]
  have ha2:0<realCoeff (planarInverse P) 2:=by
    norm_num[realCoeff,planarInverse_second_coefficient]
  exact (positiveSeriesSum_boundary_norm_lt _ _ ha Analysis.xCritical_pos_parameter
    (planarInverse_boundary_summable P).1 ha0 ha1 ha2 z hz hne).trans_le
      (planarInverse_boundary_summable P).2
end WP.PositiveConvolution

namespace WP.PositiveConvolution
open Set
lemma closedPlanarInverse_norm_lt (P:PsiTheory) (z:ℂ)
    (hz:‖z‖≤xCritical) (hne:z≠Complex.ofReal xCritical):
    ‖closedPlanarInverse P z‖<y₀:=by
  by_cases hi:‖z‖<xCritical
  · rw[closedPlanarInverse_eq_inside P z hi]
    have hs:=analytic_ball_hasSum (planarInverse P) xCritical Analysis.xCritical_pos_parameter
      (planarInverse_analyticAt P) z hi
    have hr:=planarInverse_scalar_hasSum P ‖z‖ (norm_nonneg _) hi
    have hn:‖planarInverse P z‖≤ inverseY ‖z‖:=by
      apply hs.norm_le_of_bounded hr
      intro n
      have hc:WP.coeff (planarInverse P) n=Complex.ofReal (realCoeff (planarInverse P) n):=by
        apply Complex.ext
        · rfl
        · simpa only[Complex.ofReal_im] using (planarInverse_positiveJets P).coefficient_nonneg n |>.2
      rw[hc,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg ((planarInverse_positiveJets P).coefficient_nonneg n |>.1),norm_pow]
    exact hn.trans_lt (inverseY_branch ‖z‖ ⟨norm_nonneg _,hi⟩).1.2
  · exact closedPlanarInverse_strict_boundary P z (le_antisymm hz (le_of_not_gt hi)) hne

def outerCircle (q:ℝ×ℝ):ℂ := (q.1:ℂ)*Complex.exp ((q.2:ℂ)*Complex.I)
lemma outerCircle_continuous : Continuous outerCircle:=by unfold outerCircle;fun_prop
lemma outerCircle_norm (q:ℝ×ℝ) (hq:0≤q.1):‖outerCircle q‖=q.1:=by
  simp only[outerCircle,norm_mul,Complex.norm_of_nonneg hq,Complex.norm_exp_ofReal_mul_I,mul_one]
lemma outerCircle_ne_critical (δ:ℝ) (hδ:0<δ) (q:ℝ×ℝ)
    (hq:q∈Icc (xCritical/2) xCritical ×ˢ Icc (-Real.pi) Real.pi)
    (hang:δ≤|q.2|):outerCircle q≠Complex.ofReal xCritical:=by
  intro he
  have hq0:0≤q.1:=by linarith[Analysis.xCritical_pos_parameter,hq.1.1]
  have hx:q.1=xCritical:=by
    have hh:=congrArg norm he
    rwa[outerCircle_norm q hq0,Complex.norm_of_nonneg Analysis.xCritical_pos_parameter.le] at hh
  have hcos:Real.cos q.2=1:=by
    have hh:=congrArg Complex.re he
    simp only[outerCircle,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,Complex.exp_ofReal_mul_I_re,hx] at hh
    nlinarith[Analysis.xCritical_pos_parameter]
  have ht:q.2=0:=(Real.cos_eq_one_iff_of_lt_of_lt
    (by linarith[hq.2.1,Real.pi_pos]) (by linarith[hq.2.2,Real.pi_pos])).mp hcos
  rw[ht,abs_zero] at hang
  linarith
lemma universalV_outer_uniform_bound (P:PsiTheory) (δ:ℝ) (hδ:0<δ):
    ∃C:ℝ,0<C ∧ ∀r∈Ico (xCritical/2) xCritical,∀θ:ℝ,
      θ∈Icc (-Real.pi) Real.pi→δ≤|θ|→
      ‖universalV P ((r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖≤C:=by
  let s:Set (ℝ×ℝ):=(Icc (xCritical/2) xCritical ×ˢ Icc (-Real.pi) Real.pi)∩{q|δ≤|q.2|}
  have hs:IsCompact s:=
    (isCompact_Icc.prod isCompact_Icc).inter_right (isClosed_le continuous_const (continuous_snd.abs))
  have hmap:Set.MapsTo outerCircle s (Metric.closedBall (0:ℂ) xCritical):=by
    intro q hq
    have hq0:0≤q.1:=by linarith[Analysis.xCritical_pos_parameter,hq.1.1.1]
    simpa only[Metric.mem_closedBall,dist_zero_right,outerCircle_norm q hq0] using hq.1.1.2
  have hY:ContinuousOn (fun q=>closedPlanarInverse P (outerCircle q)) s:=
    (closedPlanarInverse_continuousOn P).comp outerCircle_continuous.continuousOn hmap
  have hD:Continuous (deriv X):=by
    rw[continuous_iff_continuousAt]
    intro z
    exact (X_differentiable.analyticAt z).deriv.continuousAt
  have hnon:∀q∈s,deriv X (closedPlanarInverse P (outerCircle q))≠0:=by
    intro q hq
    exact derivX_ne_zero_of_norm_lt _ (closedPlanarInverse_norm_lt P _
      (by simpa only[Metric.mem_closedBall,dist_zero_right] using hmap hq)
      (outerCircle_ne_critical δ hδ q hq.1 hq.2))
  have hi:ContinuousOn (fun q=>(deriv X (closedPlanarInverse P (outerCircle q)))⁻¹) s:=
    (hD.continuousOn.comp hY (fun _ _=>Set.mem_univ _)).inv₀ hnon
  obtain ⟨C,hC⟩:=hs.exists_bound_of_continuousOn hi
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro r hr θ hθ hang
  have hm:(r,θ)∈s:=⟨⟨⟨hr.1,hr.2.le⟩,hθ⟩,hang⟩
  have hn:‖outerCircle (r,θ)‖<xCritical:=by
    rw[outerCircle_norm _ (by linarith[Analysis.xCritical_pos_parameter,hr.1])]
    exact hr.2
  have hid:universalV P (outerCircle (r,θ))=
      (deriv X (closedPlanarInverse P (outerCircle (r,θ))))⁻¹:=by
    rw[closedPlanarInverse_eq_inside P _ hn]
    apply eq_inv_of_mul_eq_one_left
    simpa only[mul_comm,universalV] using planar_inverse_derivative_identity P _ hn
  change ‖universalV P (outerCircle (r,θ))‖≤_
  rw[hid]
  exact (hC (r,θ) hm).trans (le_max_right _ _)
end WP.PositiveConvolution
