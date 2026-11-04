import WPFormalization.Volumes.CriticalVariance
/-! The genuine reciprocal saddle parameter is a bounded analytic unit quotient through the critical endpoint. Its physical trace is exactly one over the original Psi. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
def CriticalKernelUnits.inversePsiUnit (k:CriticalKernelUnits) (δ:ℂ):ℂ:=δ^2/k.psiUnit δ
lemma CriticalKernelUnits.inversePsiUnit_analytic (k:CriticalKernelUnits):
    AnalyticAt ℂ k.inversePsiUnit 0 := by
  apply (analyticAt_id.pow 2).div k.psiUnit_analytic
  rw[k.psiUnit_zero]
  exact_mod_cast (mul_pos (by norm_num:0<(5/2:ℝ)) y₀_pos).ne'
lemma CriticalKernelUnits.inversePsiUnit_zero (k:CriticalKernelUnits):k.inversePsiUnit 0=0 :=by
  simp[CriticalKernelUnits.inversePsiUnit]
lemma CriticalKernelUnits.inversePsiUnit_physical (k:CriticalKernelUnits):
    ∀ᶠδ:ℝ in 𝓝 0,0<δ→k.inversePsiUnit (δ:ℂ)=((1/WP.Psi (XR (y₀-δ)):ℝ):ℂ) := by
  filter_upwards[k.psiUnit_physical] with δ hδ hp
  have hn:(δ:ℂ)≠0:=by exact_mod_cast hp.ne'
  dsimp only[CriticalKernelUnits.inversePsiUnit]
  rw[hδ hp]
  push_cast
  rw[mul_comm (WP.Psi (XR (y₀-δ)):ℂ) ((δ:ℂ)^2),←div_div,div_self (pow_ne_zero 2 hn)]
lemma CriticalKernelUnits.inversePsiUnit_common_bound (k:CriticalKernelUnits):
    ∃R:ℝ,0<R ∧ R<y₀ ∧
      (∀z:ℂ,‖z‖≤R→AnalyticAt ℂ k.inversePsiUnit z ∧ ‖k.inversePsiUnit z‖≤1) ∧
      ∀δ∈Ioo (0:ℝ) R,k.inversePsiUnit (δ:ℂ)=((1/WP.Psi (XR (y₀-δ)):ℝ):ℂ) := by
  have hn:‖k.inversePsiUnit 0‖<(1:ℝ):=by rw[k.inversePsiUnit_zero,norm_zero];norm_num
  have hg:∀ᶠz:ℂ in 𝓝 0,AnalyticAt ℂ k.inversePsiUnit z ∧ ‖k.inversePsiUnit z‖≤1 := by
    filter_upwards[k.inversePsiUnit_analytic.eventually_analyticAt,
      k.inversePsiUnit_analytic.continuousAt.norm.tendsto.eventually (eventually_lt_nhds hn)] with z ha hb
    exact ⟨ha,hb.le⟩
  obtain ⟨Rg,hRg,hgood⟩:=Metric.eventually_nhds_iff.mp hg
  obtain ⟨Rp,hRp,hphysical⟩:=Metric.eventually_nhds_iff.mp k.inversePsiUnit_physical
  let R:ℝ:=min (Rg/2) (min Rp (y₀/2))
  have hR:0<R:=lt_min (half_pos hRg) (lt_min hRp (half_pos y₀_pos))
  have hRRg:R<Rg:=(min_le_left _ _).trans_lt (by linarith)
  have hRRp:R≤Rp:=(min_le_right _ _).trans (min_le_left _ _)
  have hRy:R<y₀:=((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith[y₀_pos])
  refine ⟨R,hR,hRy,?_,?_⟩
  · intro z hz
    exact hgood (by rw[dist_zero_right];exact hz.trans_lt hRRg)
  · intro δ hδ
    exact hphysical (by rw[Real.dist_eq,sub_zero,abs_of_pos hδ.1];exact hδ.2.trans_le hRRp) hδ.1
end WP.Analysis
