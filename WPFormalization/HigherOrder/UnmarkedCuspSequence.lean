import WPFormalization.HigherOrder.UnmarkedCusp
import WPFormalization.Analysis.GevreyTwoSequence
import WPFormalization.Marked.LogGrowth
noncomputable section
namespace WP.HigherOrder
open Filter
open scoped Topology
lemma unmarked_cusp_gevrey_two_sequence (P:PsiTheory):
    Analysis.GevreyTwoSequence (fun g=>(complexity g 0:ℝ))
      (fun g=>cuspCorrection P g 0 0) (formalCusp P 0 0):=by
  obtain ⟨C,B,c,H,hC,hB,hc,hH,herr⟩:=unmarked_cusp_uniform_gevrey_two P
  obtain ⟨N,hN⟩:=eventually_atTop.1 ((Analysis.complexity_real_tendsto_atTop 0).eventually (eventually_ge_atTop H))
  refine ⟨C,B,c,max N 2,hC,hB,hc,?_⟩
  intro g hg
  have hh:H≤(complexity g 0:ℝ):=hN g ((le_max_left _ _).trans hg)
  refine ⟨hH.trans_le hh,?_⟩
  intro K hK
  simpa only[Analysis.inversePowerTruncation,formalCusp,PowerSeries.coeff_mk] using
    herr g K ((le_max_right _ _).trans hg) hh hK 0 ⟨le_rfl,y₀_pos.le⟩
end WP.HigherOrder
