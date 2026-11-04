import WPFormalization.Volumes.ExtractionPhaseEuler
import WPFormalization.Volumes.LogActionComplexGerm
import WPFormalization.Analysis.PhysicalComplexInverse
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma exists_extractionS_physical_complex_germ (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    ∃S:ℂ → ℂ,AnalyticAt ℂ S (x:ℂ)∧S (x:ℂ)=(extractionS x:ℂ)∧
      deriv S (x:ℂ)=(((A (inverseY x)*r (inverseY x)*a (inverseY x))⁻¹:ℝ):ℂ)∧
      ∀ᶠt:ℝ in 𝓝 x,t∈Ico (0:ℝ) xCritical→S (t:ℂ)=(extractionS t:ℂ):=by
  have hy:=inverseY_branch x hx
  obtain ⟨G,hG,hG0,hGd,hGmatch⟩:=exists_log_action_complex_extension_at (inverseY x) hy.1
  obtain ⟨Y,hY,hY0,hYd,hYmatch⟩:=exists_physical_complex_inverse x hx
  let S:ℂ → ℂ:=fun z=>G (Y z)
  have hS:AnalyticAt ℂ S (x:ℂ):=by
    have hh:AnalyticAt ℂ G (Y (x:ℂ)):=by rw[hY0];exact hG
    exact hh.comp (f:=Y) hY
  have hSval:S (x:ℂ)=(extractionS x:ℂ):=by
    dsimp[S]
    rw[hY0,hG0]
    congr 1
    rw[extractionS,Real.log_div (marked_Z_pos 0 ⟨le_rfl,y₀_pos⟩).ne' (marked_Z_pos _ hy.1).ne']
  have hSd:deriv S (x:ℂ)=(((A (inverseY x)*r (inverseY x)*a (inverseY x))⁻¹:ℝ):ℂ):=by
    have hg:HasDerivAt G (deriv G (inverseY x:ℂ)) (Y (x:ℂ)):=by
      rw[hY0];exact hG.differentiableAt.hasDerivAt
    have hh:=hg.comp (x:ℂ) hY.differentiableAt.hasDerivAt
    have hc:deriv S (x:ℂ)=deriv G (inverseY x:ℂ)*deriv Y (x:ℂ):=by
      simpa only[Function.comp_def,S] using hh.deriv
    rw[hc,hGd,hYd]
    simp only[Complex.ofReal_inv,Complex.ofReal_mul,mul_inv_rev]
    ring
  have ht:Tendsto inverseY (𝓝 x) (𝓝 (inverseY x)):=
    (inverseY_analyticAt_interior x hx).continuousAt.tendsto
  refine ⟨S,hS,hSval,hSd,?_⟩
  filter_upwards[hYmatch,ht.eventually hGmatch] with t hy hg ht
  have hty:inverseY t∈Ico (0:ℝ) y₀:=(inverseY_branch t ht).1
  dsimp[S]
  rw[hy,hg hty.1]
  congr 1
  rw[extractionS,Real.log_div (marked_Z_pos 0 ⟨le_rfl,y₀_pos⟩).ne' (marked_Z_pos _ hty).ne']
lemma exists_extractionS_interior_complex_germ (x:ℝ) (hx:x∈Ioo (0:ℝ) xCritical):
    ∃S:ℂ → ℂ,AnalyticAt ℂ S (x:ℂ)∧S (x:ℂ)=(extractionS x:ℂ)∧
      deriv S (x:ℂ)=((WP.Psi x/x:ℝ):ℂ)∧
      ∀ᶠt:ℝ in 𝓝 x,S (t:ℂ)=(extractionS t:ℂ):=by
  obtain ⟨S,hS,hSval,hSd,hres⟩:=exists_extractionS_physical_complex_germ x ⟨hx.1.le,hx.2⟩
  have he:((A (inverseY x)*r (inverseY x)*a (inverseY x))⁻¹:ℝ)=WP.Psi x/x:=by
    apply (eq_div_iff hx.1.ne').mpr
    rw[mul_comm,←(extractionS_hasDerivAt_open x hx).deriv,extractionS_euler_eq_Psi x hx]
  refine ⟨S,hS,hSval,by simpa only[he] using hSd,?_⟩
  filter_upwards[hres,isOpen_Ioo.mem_nhds hx] with t hr ht
  exact hr ⟨ht.1.le,ht.2⟩
lemma extractionS_common_complex_extension (b:ℝ) (hb:0<b) (hbc:b<xCritical):
    ∃Ω:Set ℂ,IsOpen Ω∧(∀x∈Icc (0:ℝ) b,(x:ℂ)∈Ω)∧
      ∃S:ℂ → ℂ,AnalyticOnNhd ℂ S Ω∧∀x∈Icc (0:ℝ) b,S (x:ℂ)=(extractionS x:ℂ):=by
  apply exists_common_complex_extension 0 b (fun x:ℝ=>(extractionS x:ℂ))
  intro x hx
  obtain ⟨S,hS,hSval,hSd,hres⟩:=exists_extractionS_physical_complex_germ x ⟨hx.1,hx.2.trans_lt hbc⟩
  have he:∀ᶠt:ℝ in 𝓝 x,t∈Icc (0:ℝ) b→S (t:ℂ)=(extractionS t:ℂ):=by
    filter_upwards[hres] with t ht htb
    exact ht ⟨htb.1,htb.2.trans_lt hbc⟩
  obtain ⟨rad,hrad,hSa,hSm⟩:=complex_extension_ball_of_real_germ 0 b x
    (fun t:ℝ=>(extractionS t:ℂ)) S hS he
  exact ⟨rad,hrad,S,hSa,hSm⟩
end WP.Analysis
