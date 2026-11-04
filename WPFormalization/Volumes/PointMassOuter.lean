import WPFormalization.Volumes.CriticalPuiseux
import WPFormalization.Volumes.PlanarInverseBoundary

noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalFoldData.universalV_real_norm_lower (d:CriticalFoldData) (P:PsiTheory):
    ∃k ε0:ℝ,0<k∧0<ε0∧∀ε∈Ioo 0 ε0,
      k/Real.sqrt ε ≤ ‖universalV P ((xCritical*(1-ε):ℝ):ℂ)‖:=by
  have ht:Tendsto (fun ε:ℝ=>Complex.ofReal (Real.sqrt ε)) (𝓝[>] 0) (𝓝 (0:ℂ)):=by
    have hh:ContinuousAt (fun ε:ℝ=>Complex.ofReal (Real.sqrt ε)) 0:=by fun_prop
    simpa only[Real.sqrt_zero,Complex.ofReal_zero] using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hXi:Tendsto (fun ε:ℝ=>‖d.Ξ (Complex.ofReal (Real.sqrt ε))‖) (𝓝[>] 0) (𝓝 1):=by
    simpa only[Function.comp_def,d.Xi_zero,norm_one] using (d.Xi_analytic.continuousAt.tendsto.comp ht).norm
  have hb:∀ᶠε:ℝ in 𝓝[>] 0,(1/2:ℝ)<‖d.Ξ (Complex.ofReal (Real.sqrt ε))‖:=
    hXi.eventually (eventually_gt_nhds (by norm_num))
  have he:∀ᶠε:ℝ in 𝓝[>] 0,1/(2*d.c)/Real.sqrt ε≤
      ‖universalV P ((xCritical*(1-ε):ℝ):ℂ)‖:=by
    filter_upwards[self_mem_nhdsWithin,d.universalV_real_puiseux P,hb] with ε hε hf hbound
    rw[hf,norm_div,norm_mul,norm_inv,Complex.norm_of_nonneg d.c_pos.le,
      Complex.norm_of_nonneg (Real.sqrt_nonneg ε)]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have hh:=mul_le_mul_of_nonneg_left hbound.le (inv_nonneg.mpr d.c_pos.le)
    convert hh using 1 <;>field_simp <;>ring
  obtain ⟨ε0,hε0,he⟩:=Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp he)
  refine ⟨1/(2*d.c),ε0,one_div_pos.mpr (mul_pos (by norm_num) d.c_pos),hε0,?_⟩
  intro ε hε
  exact he (by simpa only[Real.dist_eq,sub_zero,abs_of_pos hε.1] using hε.2) hε.1
end WP.Analysis
namespace WP.PositiveConvolution
open Set
lemma universalV_outer_relative_bound (P:PsiTheory) (δ:ℝ) (hδ:0<δ):
    ∃C ε0:ℝ,0<C∧0<ε0∧ε0≤1/2∧∀ε∈Ioo 0 ε0,∀θ:ℝ,
      θ∈Icc (-Real.pi) Real.pi→δ≤|θ|→
      ‖universalV P ((xCritical*(1-ε):ℝ)*Complex.exp ((θ:ℂ)*Complex.I))/
        universalV P ((xCritical*(1-ε):ℝ):ℂ)‖≤C*Real.sqrt ε:=by
  obtain ⟨d⟩:=Analysis.exists_criticalFoldData
  obtain ⟨k,ε1,hk,hε1,hlo⟩:=d.universalV_real_norm_lower P
  obtain ⟨C,hC,habs⟩:=universalV_outer_uniform_bound P δ hδ
  refine ⟨C/k,min ε1 (1/2),div_pos hC hk,lt_min hε1 (by norm_num),min_le_right _ _,?_⟩
  intro ε hε θ hθ hang
  have hs:0<Real.sqrt ε:=Real.sqrt_pos.mpr hε.1
  have hlow:=hlo ε ⟨hε.1,hε.2.trans_le (min_le_left _ _)⟩
  have hp:0<k/Real.sqrt ε:=div_pos hk hs
  have hr:xCritical*(1-ε)∈Ico (xCritical/2) xCritical:=by
    have hhalf:ε<1/2:=hε.2.trans_le (min_le_right _ _)
    constructor
    · nlinarith[Analysis.xCritical_pos_parameter,mul_pos Analysis.xCritical_pos_parameter (show (0:ℝ)<1/2-ε by linarith)]
    · nlinarith[mul_pos Analysis.xCritical_pos_parameter hε.1]
  rw[norm_div]
  calc
    _ ≤ C / ‖universalV P ((xCritical*(1-ε):ℝ):ℂ)‖:=
      div_le_div_of_nonneg_right (habs _ hr θ hθ hang) (norm_nonneg _)
    _ ≤ C/(k/Real.sqrt ε):=div_le_div_of_nonneg_left hC.le hp hlow
    _ = C/k*Real.sqrt ε:=by field_simp
end WP.PositiveConvolution
