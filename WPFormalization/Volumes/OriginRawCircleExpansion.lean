import WPFormalization.Volumes.PhysicalRawArc
import WPFormalization.Analysis.CircleCoefficientLocalization
import WPFormalization.Analysis.FiniteModelCircleDecay
/-! The actual finite marked source on a full Cauchy circle has the original
CG3 numerator expansion at each fixed physical origin parameter. A genuine
full-circle phase bound localizes the coefficient to the actual pre-Morse
Gaussian integral. No whole-circle expansion or coefficient matching is
assumed. The Poisson denominator and final AP/raw identification are separate.
-/
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology
lemma raw_numerator_whole_circle_expansion_of_physical_source
    (P:PsiTheory)(p:ℕ)(hp:1≤p)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)
    (S Bc:ℂ→ℂ)(Γ:ℕ→ℂ→ℂ)(ρ B D:ℝ)(hxρ:x<ρ)(hB:0<B)(hD:0<D)
    (hSa:AnalyticOnNhd ℂ S (Metric.closedBall 0 ρ))
    (hBca:AnalyticOnNhd ℂ Bc (Metric.closedBall 0 ρ))
    (hΓa:∀s,AnalyticOnNhd ℂ (Γ s) (Metric.closedBall 0 ρ))
    (hSr:(fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ)))
    (hBcr:(fun t:ℝ=>Bc (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionB p t:ℂ)))
    (hΓr:∀s,(fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
      (fun t:ℝ=>(HigherOrder.markedCoefficient P p s (inverseY t):ℂ)))
    (hamp:∀s z,‖z‖≤ρ→‖Bc z*Γ s z‖≤D*B^s*(s.factorial:ℝ)^2)
    (hphase:∀θ:ℝ,(S ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))-S (x:ℂ)).re≤-(x/2)*(1-Real.cos θ))
    (N:ℕ):∀K≤N,∃C H:ℝ,0<C ∧ 0<H ∧ ∀h:ℝ,H≤h→∀k:ℕ,h*WP.Psi x=(k:ℝ)→
      ‖Complex.exp (-((h:ℂ)*S (x:ℂ)))*(x:ℂ)^k*
          WP.coeff (HigherOrder.phaseFamilyModel S (fun s z=>Bc z*Γ s z) h N) k*
          (Real.sqrt (2*Real.pi*h*WP.euler WP.Psi x):ℂ)/Bc (x:ℂ)-
        ∑j∈Finset.range (K+1),((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)/(h:ℂ)^j‖≤C/h^(K+1):=by
  have hxx:(x:ℂ)∈Metric.closedBall (0:ℂ) ρ:=by
    rw[Metric.mem_closedBall,dist_zero_right,Complex.norm_of_nonneg hx.1.le]
    exact hxρ.le
  have hBcne:Bc (x:ℂ)≠0:=by
    have hBcx:Bc (x:ℂ)=(extractionB p x:ℂ):=hBcr.self_of_nhds
    rw[hBcx]
    exact_mod_cast (extractionB_pos_interior p x ⟨hx.1.le,hx.2⟩).ne'
  have hv:0<WP.euler WP.Psi x:=mul_pos hx.1 (Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hq:0<Real.sqrt (2*Real.pi):=by positivity
  obtain ⟨β,A,R,δ,hR,hδ,hδπ,hrawid,hrawerr⟩:=physical_raw_centered_arc_data P p hp x hx S Bc Γ
    (hSa _ hxx) (hBca _ hxx) hSr hBcr (fun s=>⟨hΓa s _ hxx,hΓr s⟩) N
  let ε:ℝ:=x*δ^2/Real.pi^2
  let Dout:ℝ:=Real.sqrt (2*Real.pi)*Real.sqrt (WP.euler WP.Psi x)/‖Bc (x:ℂ)‖*(2*D)
  have hε:0<ε:=by
    dsimp[ε]
    exact div_pos (mul_pos hx.1 (pow_pos hδ 2)) (sq_pos_of_pos Real.pi_pos)
  have hbn:0<‖Bc (x:ℂ)‖:=norm_pos_iff.mpr hBcne
  have hDout:0<Dout:=by dsimp[Dout];positivity
  have hF(h:ℝ):AnalyticOnNhd ℂ (HigherOrder.phaseFamilyModel S (fun s z=>Bc z*Γ s z) h N)
      (Metric.closedBall 0 x):=by
    intro z hz
    have hzρ: z∈Metric.closedBall (0:ℂ) ρ:=(Metric.closedBall_subset_closedBall hxρ.le) hz
    apply ((analyticAt_const.mul (hSa z hzρ)).cexp).mul
    apply Finset.analyticAt_fun_sum
    intro s hs
    exact analyticAt_const.mul ((hBca z hzρ).mul (hΓa s z hzρ))
  intro K hKN
  obtain ⟨Cr,Hr,hCr,hHr,hrawerr⟩:=hrawerr K hKN
  let Ct:ℝ:=Dout*((2/ε)*(2/ε)^(K+1)*((K+1).factorial:ℝ))
  have hCt:0<Ct:=by dsimp[Ct];positivity
  refine ⟨Ct+Cr/Real.sqrt (2*Real.pi),max 1 (max Hr (2*B*((N:ℝ)+1)^2)),by positivity,
    zero_lt_one.trans_le (le_max_left _ _),?_⟩
  intro h hH k hk
  have hh1:1≤h:=(le_max_left _ _).trans hH
  have hh:0<h:=zero_lt_one.trans_le hh1
  have hHr':Hr≤h:=(le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hbudget:2*B*((N:ℝ)+1)^2≤h:=(le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hnorm:=gaussian_normalized_circle_local_error
    (HigherOrder.phaseFamilyModel S (fun s z=>Bc z*Γ s z) h N) x h (WP.euler WP.Psi x)
    (Complex.exp (-((h:ℂ)*S (x:ℂ)))) (Bc (x:ℂ)) (rawScaledGaussianIntegral β A R h) k δ
    (2*D*Real.exp (-(ε*h))) hx.1 hh hv hBcne (hF h) hδ hδπ (by positivity)
    (by simpa only[ε,neg_mul] using (phaseFamilyModel_centered_outer_bound S (fun s z=>Bc z*Γ s z) h x ρ B D δ N k hh hx.1 hxρ.le hB hD.le hbudget
      hδ hδπ hamp hphase)) (hrawid h k hh hk)
  have htail:‖Complex.exp (-((h:ℂ)*S (x:ℂ)))*(x:ℂ)^k*
      WP.coeff (HigherOrder.phaseFamilyModel S (fun s z=>Bc z*Γ s z) h N) k*
      (Real.sqrt (2*Real.pi*h*WP.euler WP.Psi x):ℂ)/Bc (x:ℂ)-
      rawScaledGaussianIntegral β A R h/(Real.sqrt (2*Real.pi):ℂ)‖≤Ct/h^(K+1):=by
    have ht:=normalized_outer_exp_factorial_bound (1/2) ε h (by norm_num) hε hh1 (K+1)
    rw[←Real.sqrt_eq_rpow] at ht
    apply hnorm.trans
    calc _=Dout*(Real.sqrt h*Real.exp (-(ε*h))):=by dsimp[Dout];ring
         _≤Dout*((2/ε)*(2/ε)^(K+1)*((K+1).factorial:ℝ)/h^(K+1)):=mul_le_mul_of_nonneg_left ht hDout.le
         _=Ct/h^(K+1):=by dsimp[Ct];ring
  have hlocal:‖rawScaledGaussianIntegral β A R h/(Real.sqrt (2*Real.pi):ℂ)-
      ∑j∈Finset.range (K+1),((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)/(h:ℂ)^j‖≤
      (Cr/Real.sqrt (2*Real.pi))/h^(K+1):=by
    have hq0:(Real.sqrt (2*Real.pi):ℂ)≠0:=by exact_mod_cast hq.ne'
    have hid:rawScaledGaussianIntegral β A R h/(Real.sqrt (2*Real.pi):ℂ)-
        ∑j∈Finset.range (K+1),((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)/(h:ℂ)^j=
        (rawScaledGaussianIntegral β A R h-(Real.sqrt (2*Real.pi):ℂ)*
          ∑j∈Finset.range (K+1),((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)/(h:ℂ)^j)/
          (Real.sqrt (2*Real.pi):ℂ):=by field_simp
    rw[hid,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq]
    exact (div_le_div_of_nonneg_right (hrawerr h hHr') hq.le).trans_eq (by ring)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add htail hlocal).trans_eq (by ring))
end WP.Analysis
