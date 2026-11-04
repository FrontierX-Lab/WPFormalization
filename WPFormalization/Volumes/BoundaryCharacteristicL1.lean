import WPFormalization.Volumes.BoundaryScaledFourierTail
import WPFormalization.Volumes.BoundaryGaussianCore
import WPFormalization.Analysis.GaussianL1Criterion
import WPFormalization.Marked.LogGrowth
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter MeasureTheory
open scoped Topology

lemma boundary_characteristic_l1_tendsto (P:PsiTheory)(p:ℕ)(hp:1≤p)(L₀:ℝ)(hL₀:0≤L₀)
    (gs:ℕ→ℕ)(hg:Tendsto gs atTop atTop)(xs:ℕ→ℝ)
    (hx:∀j,xs j∈Ioo (0:ℝ) xCritical)(Ls:ℕ→Fin p→ℝ)(hL:∀j i,Ls j i∈Icc 0 L₀)
    (hmu:Tendsto (fun j=>(complexity (gs j) p:ℝ)*Psi (xs j)) atTop atTop) :
    Tendsto (fun j=>∫t:ℝ,‖scaledBoundaryFourier P (gs j) p (Ls j) (xs j) t-
      Complex.exp (-(t:ℂ)^2/2)‖) atTop (𝓝 0) := by
  obtain ⟨c,C,hc,hC,htail⟩:=scaledBoundaryFourier_uniform_tail P
  apply Analysis.gaussian_characteristic_l1_tendsto_of_core_tails
    (fun j=>scaledBoundaryFourier P (gs j) p (Ls j) (xs j))
    (fun j=>scaledBoundaryFourier_integrable P (gs j) p (Ls j) (xs j) (hx j)) c C hc
  · exact boundary_characteristic_gaussian_core_tendsto P p hp L₀ hL₀ gs hg xs hx Ls hL hmu
  · intro T hT
    have hh:Tendsto (fun j=>(complexity (gs j) p:ℝ)) atTop atTop:=
      (Analysis.complexity_real_tendsto_atTop p).comp hg
    filter_upwards [hg.eventually_ge_atTop 2,hh.eventually_ge_atTop 32,hh.eventually_ge_atTop (T^2)]
      with j hj hhj hTj
    have hs:Stable (gs j) p:=by unfold Stable;omega
    have hn:32≤complexity (gs j) p:=by exact_mod_cast hhj
    exact htail (gs j) p hp hs hn (Ls j) (xs j) (hx j) T (by linarith) hTj

end WP.BoundaryConvolution
