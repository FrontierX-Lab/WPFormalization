import WPFormalization.Analysis.OriginStandardGaussian
import WPFormalization.Analysis.ExtractionFactorization
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma origin_real_tilt_domain (p:ℕ) (S Bc:ℂ→ℂ) (η₀ ρ:ℝ) (hη₀:0<η₀) (hρ:0<ρ)
    (hSr:∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ))
    (hBr:∀ᶠt:ℝ in 𝓝 0,0≤t→Bc (t:ℂ)=(extractionB p t:ℂ)):
    ∃η:ℝ,0<η∧η≤η₀∧η<xCritical∧
      (∀x∈Ioo (0:ℝ) η,1≤deriv WP.Psi x∧S (x:ℂ)=(extractionS x:ℂ)∧Bc (x:ℂ)=(extractionB p x:ℂ))∧
      ∀(h x w:ℝ),0<h→x∈Ioo (0:ℝ) η→|w|≤ρ*Real.sqrt (h*x)→
        let y:ℝ:=x*Real.exp (w/Real.sqrt (h*WP.euler WP.Psi x));
        y∈Ioo (0:ℝ) xCritical∧S (y:ℂ)=(extractionS y:ℂ)∧Bc (y:ℂ)=(extractionB p y:ℂ):=by
  have hP:AnalyticAt ℝ WP.Psi 0:=Psi_origin_analytic.1
  have hβ:∀ᶠx:ℝ in 𝓝 0,1<deriv WP.Psi x:=
    hP.deriv.continuousAt.tendsto.eventually (eventually_gt_nhds (by rw[Psi_deriv_zero_value];norm_num))
  obtain ⟨r,hr,hloc⟩:=Metric.eventually_nhds_iff.mp ((hSr.and hBr).and hβ)
  let η:ℝ:=min (η₀/2) (min (r/2) (min (r/(2*Real.exp ρ)) (xCritical/(2*Real.exp ρ))))
  have hxcrit:=xCritical_pos_parameter
  have hη:0<η:=by dsimp[η];positivity
  have hη₀:η≤η₀:=(min_le_left _ _).trans (by linarith)
  have hηr:η<r:=((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hηer:η*(2*Real.exp ρ)≤r:=by
    apply (le_div_iff₀ (by positivity:0<2*Real.exp ρ)).mp
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hηex:η*(2*Real.exp ρ)≤xCritical:=by
    apply (le_div_iff₀ (by positivity:0<2*Real.exp ρ)).mp
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hηx:η<xCritical:=by
    have he:1<Real.exp ρ:=(Real.one_lt_exp_iff).mpr hρ
    nlinarith
  have hbase(x:ℝ)(hx:x∈Ioo (0:ℝ) η):1≤deriv WP.Psi x∧S (x:ℂ)=(extractionS x:ℂ)∧Bc (x:ℂ)=(extractionB p x:ℂ):=by
    have hl:=hloc (show dist x 0<r by rw[Real.dist_eq,sub_zero,abs_of_pos hx.1];exact hx.2.trans hηr)
    exact ⟨hl.2.le,hl.1.1 hx.1.le,hl.1.2 hx.1.le⟩
  refine ⟨η,hη,hη₀,hηx,hbase,?_⟩
  intro h x w hh hx hw
  let σ:ℝ:=Real.sqrt (h*WP.euler WP.Psi x)
  have hv:x≤WP.euler WP.Psi x:=by
    have hder:1≤deriv WP.Psi x:=(hbase x hx).1
    change x≤x*deriv WP.Psi x
    nlinarith[hx.1]
  have hσ:Real.sqrt (h*x)≤σ:=Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hv hh.le)
  have hσp:0<σ:=(Real.sqrt_pos.mpr (mul_pos hh hx.1)).trans_le hσ
  have hwσ:|w/σ|≤ρ:=by
    rw[abs_div,abs_of_pos hσp]
    apply (div_le_iff₀ hσp).mpr
    exact hw.trans (mul_le_mul_of_nonneg_left hσ hρ.le)
  have hex:Real.exp (w/σ)≤Real.exp ρ:=Real.exp_le_exp.mpr ((le_abs_self _).trans hwσ)
  let y:ℝ:=x*Real.exp (w/σ)
  have hyp:0<y:=mul_pos hx.1 (Real.exp_pos _)
  have hyη:y<η*Real.exp ρ:=by
    calc
      _≤x*Real.exp ρ:=mul_le_mul_of_nonneg_left hex hx.1.le
      _<η*Real.exp ρ:=mul_lt_mul_of_pos_right hx.2 (Real.exp_pos _)
  have hyr:y<r:=by nlinarith
  have hyx:y<xCritical:=by nlinarith
  have hl:=hloc (show dist y 0<r by rw[Real.dist_eq,sub_zero,abs_of_pos hyp];exact hyr)
  exact ⟨⟨hyp,hyx⟩,hl.1.1 hyp.le,hl.1.2 hyp.le⟩
lemma leading_model_real_ratio (g p:ℕ) (hs:Stable g p) (S Bc:ℂ→ℂ) (x y:ℝ)
    (hx:x∈Ico (0:ℝ) xCritical) (hy:y∈Ico (0:ℝ) xCritical)
    (hSx:S (x:ℂ)=(extractionS x:ℂ)) (hSy:S (y:ℂ)=(extractionS y:ℂ))
    (hBx:Bc (x:ℂ)=(extractionB p x:ℂ)) (hBy:Bc (y:ℂ)=(extractionB p y:ℂ)):
    (Complex.exp ((complexity g p:ℂ)*S (y:ℂ))*Bc (y:ℂ))/
      (Complex.exp ((complexity g p:ℂ)*S (x:ℂ))*Bc (x:ℂ))=
      ((markedModel g p (inverseY y)/markedModel g p (inverseY x):ℝ):ℂ):=by
  have hix:=inverseY_branch x hx
  have hiy:=inverseY_branch y hy
  have hfx:=extraction_factorization_proof g p (inverseY x) hix.1
  have hfy:=extraction_factorization_proof g p (inverseY y) hiy.1
  rw[hix.2] at hfx
  rw[hiy.2] at hfy
  have hM0:markedModel g p 0≠0:=(markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
  rw[hSx,hSy,hBx,hBy,←Complex.ofReal_natCast,←Complex.ofReal_mul,←Complex.ofReal_mul,
    ←Complex.ofReal_exp,←Complex.ofReal_exp,←Complex.ofReal_mul,←Complex.ofReal_mul,←Complex.ofReal_div]
  apply congrArg Complex.ofReal
  rw[hfx,hfy]
  field_simp
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma origin_standard_gaussian_physical_data (p:ℕ) (S Bc:ℂ→ℂ)
    (hS:AnalyticAt ℂ S 0) (hSd:deriv S 0=2) (hBc:AnalyticAt ℂ Bc 0) (hBc0:Bc 0≠0)
    (hSr:∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ))
    (hBr:∀ᶠt:ℝ in 𝓝 0,0≤t→Bc (t:ℂ)=(extractionB p t:ℂ)):
    ∃(G Amp:ℂ × ℂ → ℂ)(η ρ C D K:ℝ),0<η∧η<xCritical∧0<ρ∧0<C∧0<D∧0<K∧
      (∀x:ℝ,x∈Ioo (0:ℝ) η→1≤deriv WP.Psi x∧WP.Psi x≤K*x)∧
      (∀(h x:ℝ),0<h→x∈Ioo (0:ℝ) η→
        AnalyticOnNhd ℂ (originStandardLog G h x) (Metric.ball 0 (ρ*Real.sqrt (h*x)))∧
        AnalyticOnNhd ℂ (originStandardAmplitude Amp h x) (Metric.ball 0 (ρ*Real.sqrt (h*x)))∧
        WP.coeff (originStandardLog G h x) 0=0∧WP.coeff (originStandardLog G h x) 1=0∧
        WP.coeff (originStandardLog G h x) 2=1/2∧originStandardAmplitude Amp h x 0=1∧
        ∀w:ℂ,‖w‖≤ρ*Real.sqrt (h*x)→
          ‖originStandardLog G h x w‖≤C*‖w‖^2∧‖originStandardAmplitude Amp h x w‖≤D∧
          let z:ℂ:=(x:ℂ)*Complex.exp (w/(Real.sqrt (h*WP.euler WP.Psi x):ℂ));
          Complex.exp (-(h:ℂ)*(WP.Psi x:ℂ)*(w/(Real.sqrt (h*WP.euler WP.Psi x):ℂ)))*
            ((Complex.exp ((h:ℂ)*S z)*Bc z)/(Complex.exp ((h:ℂ)*S (x:ℂ))*Bc (x:ℂ)))=
              Complex.exp (originStandardLog G h x w)*originStandardAmplitude Amp h x w)∧
      ∀(h x w:ℝ),0<h→x∈Ioo (0:ℝ) η→|w|≤ρ*Real.sqrt (h*x)→
        let y:ℝ:=x*Real.exp (w/Real.sqrt (h*WP.euler WP.Psi x));
        y∈Ioo (0:ℝ) xCritical∧S (y:ℂ)=(extractionS y:ℂ)∧Bc (y:ℂ)=(extractionB p y:ℂ)∧
        ∀g:ℕ,Stable g p→h=(complexity g p:ℝ)→
          (Complex.exp ((h:ℂ)*S (y:ℂ))*Bc (y:ℂ))/
            (Complex.exp ((h:ℂ)*S (x:ℂ))*Bc (x:ℂ))=
              ((markedModel g p (inverseY y)/markedModel g p (inverseY x):ℝ):ℂ):=by
  obtain ⟨G,Amp,η₀,ρ,C,D,K,hη₀,hη₀x,hρ,hC,hD,hK,hmean,hstd⟩:=
    origin_standard_gaussian_data_of_physical_source S Bc hS hSd hBc hBc0 hSr
  obtain ⟨η,hη,hηη₀,hηx,hbase,htilt⟩:=origin_real_tilt_domain p S Bc η₀ ρ hη₀ hρ hSr hBr
  have hxin(x:ℝ)(hx:x∈Ioo (0:ℝ) η):x∈Ioo (0:ℝ) η₀:=⟨hx.1,hx.2.trans_le hηη₀⟩
  refine ⟨G,Amp,η,ρ,C,D,K,hη,hηx,hρ,hC,hD,hK,?_,?_,?_⟩
  · intro x hx
    exact ⟨(hbase x hx).1,hmean x (hxin x hx)⟩
  · intro h x hh hx
    exact hstd h x hh (hxin x hx)
  · intro h x w hh hx hw
    have hy:=htilt h x w hh hx hw
    refine ⟨hy.1,hy.2.1,hy.2.2,?_⟩
    intro g hs hheq
    subst h
    exact leading_model_real_ratio g p hs S Bc x _ ⟨hx.1.le,hx.2.trans hηx⟩
      ⟨hy.1.1.le,hy.1.2⟩ (hbase x hx).2.1 hy.2.1 (hbase x hx).2.2 hy.2.2
end WP.Analysis
namespace WP.Analysis
lemma origin_complex_tilt_norm (h x ρ:ℝ) (w:ℂ) (hh:0<h) (hx:0<x) (hρ:0≤ρ)
    (hder:1≤deriv WP.Psi x) (hw:‖w‖≤ρ*Real.sqrt (h*x)):
    ‖(x:ℂ)*Complex.exp (w/(Real.sqrt (h*WP.euler WP.Psi x):ℂ))‖≤x*Real.exp ρ:=by
  have hv:x≤WP.euler WP.Psi x:=by
    change x≤x*deriv WP.Psi x
    nlinarith
  have hσ:Real.sqrt (h*x)≤Real.sqrt (h*WP.euler WP.Psi x):=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hv hh.le)
  have hσp:0<Real.sqrt (h*WP.euler WP.Psi x):=(Real.sqrt_pos.mpr (mul_pos hh hx)).trans_le hσ
  have harg:‖w/(Real.sqrt (h*WP.euler WP.Psi x):ℂ)‖≤ρ:=by
    rw[norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hσp]
    apply (div_le_iff₀ hσp).mpr
    exact hw.trans (mul_le_mul_of_nonneg_left hσ hρ)
  rw[norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx]
  exact mul_le_mul_of_nonneg_left
    ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr harg)) hx.le
end WP.Analysis
