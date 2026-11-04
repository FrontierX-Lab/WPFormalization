import WPFormalization.Analysis.PoissonNormalizerLower
import WPFormalization.Volumes.OriginModelGaussianTail
import WPFormalization.Analysis.OriginPhaseCircleDecay
/-! The actual extractionQ has a factorial lower bound uniformly for
0 <= k <= kappa*sqrt(h), with a separate exact zero-frequency branch.
All source trace hypotheses are proved fields of StrongOptimalModel. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma Psi_origin_lower:
    ∃r:ℝ,0<r ∧ r<xCritical ∧ ∀x∈Icc (0:ℝ) r,x≤Psi x:=by
  have ha:=Psi_analyticAt_interior 0 ⟨le_rfl,xCritical_pos_parameter⟩
  have hzero:(1:ℝ)<deriv Psi 0:=by rw[Psi_deriv_zero_value];norm_num
  have hnear:∀ᶠx:ℝ in 𝓝 0,1<deriv Psi x:=
    ha.deriv.continuousAt.tendsto.eventually (eventually_gt_nhds hzero)
  obtain ⟨R,hR,hball⟩:=Metric.eventually_nhds_iff.mp hnear
  let r:ℝ:=min (R/2) (xCritical/2)
  have hr:0<r:=lt_min (by positivity) (div_pos xCritical_pos_parameter (by norm_num))
  have hrx:r<xCritical:=(min_le_right _ _).trans_lt (by linarith[xCritical_pos_parameter])
  have hder:∀x∈Icc (0:ℝ) r,1≤deriv Psi x:=by
    intro x hx
    apply (hball _).le
    rw[Real.dist_eq,sub_zero,abs_of_nonneg hx.1]
    have hxr:x≤R/2:=hx.2.trans (min_le_left _ _)
    linarith
  have hmono:MonotoneOn (fun x:ℝ=>Psi x-x) (Icc (0:ℝ) r):=by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
    · apply ContinuousOn.sub
      · intro x hx
        exact (Psi_analyticAt_interior x ⟨hx.1,hx.2.trans_lt hrx⟩).continuousAt.continuousWithinAt
      · exact continuous_id.continuousOn
    · intro x hx
      rw[interior_Icc] at hx
      exact ((Psi_analyticAt_interior x ⟨hx.1.le,hx.2.trans hrx⟩).differentiableAt.sub differentiableAt_id).differentiableWithinAt
    · intro x hx
      rw[interior_Icc] at hx
      have he:deriv (fun x:ℝ=>Psi x-x) x=deriv Psi x-1:=by
        convert! ((Psi_analyticAt_interior x ⟨hx.1.le,hx.2.trans hrx⟩).differentiableAt.hasDerivAt.sub (hasDerivAt_id x)).deriv using 1 <;>rfl
      rw[he]
      have hd:=hder x ⟨hx.1.le,hx.2.le⟩
      linarith
  refine ⟨r,hr,hrx,?_⟩
  intro x hx
  have ht:=hmono ⟨le_rfl,hr.le⟩ hx hx.1
  change Psi 0-0≤Psi x-x at ht
  rw[Psi_zero_value,sub_self] at ht
  linarith

lemma origin_normalizer_data_of_source (p:ℕ)(S Bc:ℂ→ℂ)(ρs:ℝ)
    (hρs:0<ρs)(hρsx:ρs<xCritical)(hS:AnalyticAt ℂ S 0)(hS0:S 0=0)(hSd:deriv S 0=2)
    (hSr:∀x∈Icc (0:ℝ) ρs,S (x:ℂ)=(extractionS x:ℂ))
    (hBr:∀x∈Icc (0:ℝ) ρs,Bc (x:ℂ)=(extractionB p x:ℂ))
    (hBn:∀x∈Icc (0:ℝ) ρs,‖Bc (x:ℂ)-1‖≤1/2):
    ∃r C:ℝ,0<r ∧ r<ρs ∧ 0<C ∧ ∀x∈Icc (0:ℝ) r,
      2*x-C*x^2≤extractionS x ∧ x≤Psi x ∧ euler Psi x≤4*x ∧ 1/2≤extractionB p x:=by
  obtain ⟨R,C,hR,hC,hrem⟩:=complex_analytic_uniform_linear_remainder S hS
  obtain ⟨rP,hrP,hrPx,hPsi⟩:=Psi_origin_lower
  obtain ⟨rV,hrV,hrVx,hV⟩:=eulerPsi_origin_upper
  let r:ℝ:=min (ρs/2) (min (R/2) (min rP rV))
  have hr:0<r:=lt_min (by positivity) (lt_min (by positivity) (lt_min hrP hrV))
  have hrs:r<ρs:=(min_le_left _ _).trans_lt (by linarith)
  have hrR:r<R:=((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hrP':r≤rP:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrV':r≤rV:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨r,C,hr,hrs,hC,?_⟩
  intro x hx
  have hxs:x∈Icc (0:ℝ) ρs:=⟨hx.1,hx.2.trans hrs.le⟩
  have hxt:‖(x:ℂ)‖<R:=by rw[Complex.norm_of_nonneg hx.1];exact hx.2.trans_lt hrR
  have ht:=hrem 0 (x:ℂ) (by simpa using hR) hxt
  have he:S (x:ℂ)-S 0-deriv S 0*((x:ℂ)-0)=((extractionS x-2*x:ℝ):ℂ):=by
    rw[hSr x hxs,hS0,hSd]
    push_cast
    ring
  rw[he,Complex.norm_real,Real.norm_eq_abs,sub_zero,Complex.norm_of_nonneg hx.1] at ht
  have hB:=hBn x hxs
  rw[hBr x hxs,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hB
  refine ⟨?_,hPsi x ⟨hx.1,hx.2.trans hrP'⟩,hV x ⟨hx.1,hx.2.trans hrV'⟩,?_⟩
  · have hh:=(abs_le.mp ht).1
    linarith
  · have hh:=(abs_le.mp hB).1
    linarith

lemma tiny_frequency_density_saddle (r κ:ℝ)(hr:0<r)(hrx:r<xCritical)(hκ:0≤κ)
    (hPr:r≤Psi r):
    ∃H:ℝ,0<H ∧ ∀h:ℝ,H≤h→∀k:ℕ,0<k→(k:ℝ)≤κ*Real.sqrt h→
      XR (densityY (2*((k:ℝ)/h)))∈Ioo (0:ℝ) r:=by
  have ht:Tendsto (fun h:ℝ=>κ/Real.sqrt h) atTop (𝓝 (0:ℝ)):=by
    simpa only[Function.comp_def,div_eq_mul_inv,mul_zero] using (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul κ
  obtain ⟨H0,hH0⟩:=eventually_atTop.1 (ht.eventually (eventually_lt_nhds hr))
  let H:ℝ:=max H0 1
  have hH:0<H:=lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨H,hH,?_⟩
  intro h hh k hk hks
  have hhp:0<h:=hH.trans_le hh
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hhp
  have hsmall:κ/Real.sqrt h<r:=hH0 h ((le_max_left _ _).trans hh)
  have hν:0<(k:ℝ)/h:=div_pos (by exact_mod_cast hk) hhp
  have hνs:(k:ℝ)/h≤κ/Real.sqrt h:=by
    apply (div_le_div_iff₀ hhp hs).mpr
    calc
      _≤(κ*Real.sqrt h)*Real.sqrt h:=mul_le_mul_of_nonneg_right hks hs.le
      _=κ*h:=by rw[mul_assoc,←pow_two,Real.sq_sqrt hhp.le]
  have hroot:=physicalDensitySaddle_spec ((k:ℝ)/h) hν
  refine ⟨hroot.1.1,?_⟩
  by_contra hnot
  have hxr:r≤XR (densityY (2*((k:ℝ)/h))):=not_lt.mp hnot
  have hm:=Psi_strictMonoOn.monotoneOn ⟨hr,hrx⟩ hroot.1 hxr
  rw[hroot.2] at hm
  exact (not_lt_of_ge (hPr.trans hm)) (hνs.trans_lt hsmall)

lemma extractionQ_normalized_tiny_lower_of_source (p:ℕ)(S Bc:ℂ→ℂ)(ρs κ:ℝ)
    (hρs:0<ρs)(hρsx:ρs<xCritical)(hκ:0<κ)
    (hS:AnalyticAt ℂ S 0)(hS0:S 0=0)(hSd:deriv S 0=2)
    (hSr:∀x∈Icc (0:ℝ) ρs,S (x:ℂ)=(extractionS x:ℂ))
    (hBr:∀x∈Icc (0:ℝ) ρs,Bc (x:ℂ)=(extractionB p x:ℂ))
    (hBn:∀x∈Icc (0:ℝ) ρs,‖Bc (x:ℂ)-1‖≤1/2):
    ∃cQ H:ℝ,0<cQ ∧ 0<H ∧ ∀g:ℕ,H≤(complexity g p:ℝ)→∀k:ℕ,
      (k:ℝ)≤κ*Real.sqrt (complexity g p:ℝ)→
      cQ*(2*(complexity g p:ℝ))^k/(k.factorial:ℝ)≤
        Real.pi*extractionQ g p k/markedModel g p 0:=by
  obtain ⟨r,C,hr,hrs,hC,hdata⟩:=origin_normalizer_data_of_source p S Bc ρs hρs hρsx hS hS0 hSd hSr hBr hBn
  have hrx:r<xCritical:=hrs.trans hρsx
  have hPr:r≤Psi r:=(hdata r ⟨hr.le,le_rfl⟩).2.1
  obtain ⟨H,hH,hfreq⟩:=tiny_frequency_density_saddle r κ hr hrx hκ.le hPr
  let cQ:ℝ:=Real.exp (-C*κ^2)/4
  have hcQ:0<cQ:=by dsimp[cQ];positivity
  have hcQ1:cQ≤1:=by
    have he:Real.exp (-C*κ^2)≤1:=Real.exp_le_one_iff.mpr (by nlinarith[mul_nonneg hC.le (sq_nonneg κ)])
    dsimp[cQ]
    linarith
  refine ⟨cQ,H,hcQ,hH,?_⟩
  intro g hg k hk
  let h:ℝ:=complexity g p
  have hh:0<h:=hH.trans_le hg
  have hst:Stable g p:=by
    have hn:0<complexity g p:=by exact_mod_cast (show (0:ℝ)<(complexity g p:ℝ) from hh)
    unfold Stable complexity at *
    omega
  have hM0:markedModel g p 0≠0:=(markedModel_pos_parameter g p hst 0 ⟨le_rfl,y₀_pos⟩).ne'
  by_cases hk0:k=0
  · subst k
    simp only[pow_zero,mul_one,Nat.factorial_zero,Nat.cast_one,div_one]
    have he:Real.pi*extractionQ g p 0/markedModel g p 0=1:=by
      rw[extractionQ_zero_exact]
      field_simp [hM0,Real.pi_ne_zero]
    rw[he]
    exact hcQ1
  have hkpos:0<k:=Nat.pos_of_ne_zero hk0
  let ν:ℝ:=(k:ℝ)/h
  let x:ℝ:=XR (densityY (2*ν))
  have hx:x∈Ioo (0:ℝ) r:=hfreq h hg k hkpos hk
  have hν:0<ν:=div_pos (by exact_mod_cast hkpos) hh
  have hroot:=physicalDensitySaddle_spec ν hν
  have hd:=hdata x ⟨hx.1.le,hx.2.le⟩
  have hxk:h*x≤(k:ℝ):=by
    calc
      _≤h*Psi x:=mul_le_mul_of_nonneg_left hd.2.1 hh.le
      _=(k:ℝ):=by rw[hroot.2];dsimp[ν];field_simp
  have hv:0<euler Psi x:=mul_pos hx.1 (Psi_deriv_pos_interior x ⟨hx.1.le,hx.2.trans hrx⟩)
  have hn:=poisson_saddle_normalizer_lower h x (extractionS x) (extractionB p x) (euler Psi x) C κ k
    hh hx.1 hv hkpos hC.le hκ.le hd.1 hd.2.2.2 hxk hk hd.2.2.1
  have hf:=extractionQ_factorization_positive g p k hk0 hh
  have he:Real.pi*extractionQ g p k/markedModel g p 0=
      (Real.exp (h*extractionS x)*x⁻¹^k*poissonCenter k)*
        (extractionB p x*Real.sqrt (ν/euler Psi x)):=by
    rw[hf]
    dsimp only[h,ν,x]
    field_simp [hM0,Real.pi_ne_zero]
  rw[he]
  exact hn
end WP.Analysis
