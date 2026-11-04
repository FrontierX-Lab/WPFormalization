import WPFormalization.HigherOrder.OptimalMarkedBudget
import WPFormalization.HigherOrder.OriginPoissonNormalization
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
def originPoissonParameter (S:ℂ→ℂ) (z:ℂ):ℂ:=X z*deriv S (X z)
def originExtractedCoefficientFamily (P:PsiTheory) (p:ℕ) (S Bc:ℂ→ℂ)
    (L:ℕ→ℂ→ℂ) (Z:ℂ × ℂ → ℂ) (n:ℕ) (z:ℂ):ℂ:=
  normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n (originPoissonParameter S z)
lemma originPoissonParameter_zero (S:ℂ→ℂ):originPoissonParameter S 0=0:=by
  simp[originPoissonParameter,X]
lemma originPoissonParameter_analyticAt_zero (S:ℂ→ℂ) (hS:AnalyticAt ℂ S 0):
    AnalyticAt ℂ (originPoissonParameter S) 0:=by
  have hX0:X 0=0:=by simp[X]
  have hSd:AnalyticAt ℂ (deriv S) (X 0):=by simpa only[hX0] using hS.deriv
  exact (X_differentiable.analyticAt 0).mul (hSd.comp (X_differentiable.analyticAt 0))
lemma originPoissonParameter_real_germ (S:ℂ→ℂ) (hS:AnalyticAt ℂ S 0)
    (hSr:∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ)):
    ∀ᶠY:ℝ in 𝓝 0,Y∈Icc (0:ℝ) y₀→ originPoissonParameter S (Y:ℂ)=((density Y/2:ℝ):ℂ):=by
  have hE:=Analysis.extractionS_origin_complex_euler S hS hSr
  have hT:Tendsto XR (𝓝 (0:ℝ)) (𝓝 (0:ℝ)):=by
    simpa only[XR_zero] using XR_continuous.continuousAt.tendsto (x:=(0:ℝ))
  filter_upwards[hT.eventually hE] with Y hE hY
  have hXr:X (Y:ℂ)=(XR Y:ℂ):=by
    apply Complex.ext
    · rfl
    · simp only[X_im_ofReal,Complex.ofReal_im]
  have hxr:0≤XR Y:=by
    rw[←XR_zero]
    exact XR_strictMonoOn.monotoneOn y₀_pos.le hY.2 hY.1
  unfold originPoissonParameter
  rw[hXr,hE hxr,WP.Psi,Analysis.inverseY_eq_of_root _ _ hY.2 rfl]
lemma originExtractedCoefficientFamily_parameter_extension (P:PsiTheory) (p:ℕ)
    (S Bc:ℂ→ℂ) (L:ℕ→ℂ→ℂ) (Z:ℂ × ℂ → ℂ) (ν₀ C B:ℝ)
    (hν₀:0<ν₀) (hS:AnalyticAt ℂ S 0)
    (hSr:∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ))
    (hcoef:∀n,AnalyticOnNhd ℂ (normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n)
        (Metric.ball 0 ν₀)∧∀ν:ℂ,‖ν‖<ν₀→
        ‖normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n ν‖≤C*B^n*(n.factorial:ℝ)^2)
    (hzero:∀n,normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n 0=
      (markedCoefficient P p n 0:ℂ)):
    ∃η:ℝ,0<η∧η<y₀∧
      (∀z:ℂ,‖z‖≤η→‖originPoissonParameter S z‖<ν₀)∧
      (∀n,AnalyticOnNhd ℂ (originExtractedCoefficientFamily P p S Bc L Z n) (Metric.ball 0 η)∧
        ∀z:ℂ,‖z‖≤η→‖originExtractedCoefficientFamily P p S Bc L Z n z‖≤C*B^n*(n.factorial:ℝ)^2)∧
      (∀n,originExtractedCoefficientFamily P p S Bc L Z n 0=(markedCoefficient P p n 0:ℂ))∧
      ∀n Y,Y∈Icc (0:ℝ) η→ originExtractedCoefficientFamily P p S Bc L Z n (Y:ℂ)=
        normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n (((density Y/2:ℝ):ℂ)):=by
  have hμ:=originPoissonParameter_analyticAt_zero S hS
  have hμn:∀ᶠz:ℂ in 𝓝 0,‖originPoissonParameter S z‖<ν₀:=
    hμ.continuousAt.norm.tendsto.eventually (eventually_lt_nhds (by rw[originPoissonParameter_zero,norm_zero];exact hν₀))
  obtain ⟨r,hr,hlocal⟩:=Metric.eventually_nhds_iff.mp (hμ.eventually_analyticAt.and hμn)
  obtain ⟨s,hs,hreal⟩:=Metric.eventually_nhds_iff.mp (originPoissonParameter_real_germ S hS hSr)
  let η:ℝ:=min (r/2) (min (s/2) (y₀/2))
  have hη:0<η:=lt_min (half_pos hr) (lt_min (half_pos hs) (half_pos y₀_pos))
  have hηr:η<r:=(min_le_left _ _).trans_lt (half_lt_self hr)
  have hηs:η<s:=((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hs)
  have hηy:η<y₀:=((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self y₀_pos)
  have hpoint(z:ℂ) (hz:‖z‖≤η):AnalyticAt ℂ (originPoissonParameter S) z∧‖originPoissonParameter S z‖<ν₀:=
    hlocal (by simpa only[dist_zero_right] using hz.trans_lt hηr)
  refine ⟨η,hη,hηy,(fun z hz=>(hpoint z hz).2),?_,?_,?_⟩
  · intro n
    constructor
    · intro z hz
      have hzn:‖z‖≤η:=(show ‖z‖<η by simpa only[Metric.mem_ball,dist_zero_right] using hz).le
      have hp:=hpoint z hzn
      exact ((hcoef n).1 _ (by simpa only[Metric.mem_ball,dist_zero_right] using hp.2)).comp hp.1
    · intro z hz
      exact (hcoef n).2 _ (hpoint z hz).2
  · intro n
    exact (congrArg (normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n)
      (originPoissonParameter_zero S)).trans (hzero n)
  · intro n Y hY
    have he:=hreal (show dist Y 0<s by rw[Real.dist_eq,sub_zero,abs_of_nonneg hY.1];exact hY.2.trans_lt hηs)
      ⟨hY.1,hY.2.trans hηy.le⟩
    unfold originExtractedCoefficientFamily
    rw[he]
end WP.HigherOrder
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma actual_origin_poisson_parameter_family (P:PsiTheory) (p:ℕ) (hp:1≤p):
    ∃(S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(Z:ℂ × ℂ → ℂ)(η C B B₀ κ H:ℝ),
      0<η∧η<y₀∧0<C∧0<B∧0<B₀∧0<κ∧0<H∧
      AnalyticAt ℂ S 0∧S 0=0∧deriv S 0=2∧Bc 0=1∧
      (∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ))∧
      (∀g:ℕ,H≤(complexity g p:ℝ)→
        2*B₀*((⌊κ*Real.sqrt (complexity g p:ℝ)⌋₊:ℝ)+1)^2≤(complexity g p:ℝ))∧
      (∀n,AnalyticOnNhd ℂ (originExtractedCoefficientFamily P p S Bc L Z n) (Metric.ball 0 η)∧
        ∀z:ℂ,‖z‖≤η→‖originExtractedCoefficientFamily P p S Bc L Z n z‖≤C*B^n*(n.factorial:ℝ)^2)∧
      (∀n,originExtractedCoefficientFamily P p S Bc L Z n 0=(markedCoefficient P p n 0:ℂ))∧
      ∀n Y,Y∈Icc (0:ℝ) η→ originExtractedCoefficientFamily P p S Bc L Z n (Y:ℂ)=
        normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n (((density Y/2:ℝ):ℂ)):=by
  obtain ⟨Ω,L,C₀,B₀,κ,a,H,hΩ,hcover,hC₀,hB₀,hκ,ha,hH,hLa,hL0,hLr,hLb,hmodels⟩:=
    optimal_marked_model_real_comparison_with_budget P p hp
  obtain ⟨S,Bc,Z,R,ν₀,ρ,A,C,B,hR,hν₀,hν₀R,hρ,hA,hC,hB,hS,hS0,hSd,hBc0,hSr,
    hHa,hHr,hfa,hfb,hcoef,hzero,hfinal⟩:=
      actual_origin_poisson_normalized_model_data_of_parameter_data P p Ω L C₀ B₀ hΩ hcover hC₀ hB₀ hLa hLr hLb
  obtain ⟨η,hη,hηy,hparam,hfamily,hfzero,htrace⟩:=
    originExtractedCoefficientFamily_parameter_extension P p S Bc L Z ν₀ C B hν₀ hS hSr hcoef hzero
  exact ⟨S,Bc,L,Z,η,C,B,B₀,κ,H,hη,hηy,hC,hB,hB₀,hκ,hH,hS,hS0,hSd,hBc0,hLr,
    (fun g hg=>(hmodels g hg).1),hfamily,hfzero,htrace⟩
end WP.HigherOrder
