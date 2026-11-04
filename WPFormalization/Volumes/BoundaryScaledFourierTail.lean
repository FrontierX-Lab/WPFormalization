import WPFormalization.Volumes.BoundaryFourierInversion
import WPFormalization.Volumes.BoundaryFourierTail
import WPFormalization.Analysis.ScaledFourierTail
noncomputable section
namespace WP.BoundaryConvolution
open Set MeasureTheory
lemma scaledBoundaryFourier_uniform_tail (P:PsiTheory):
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀g p:ℕ,1≤p→Stable g p→32≤complexity g p→
      ∀L:Fin p→ℝ,∀x∈Ioo (0:ℝ) xCritical,∀T:ℝ,0≤T→T^2≤(complexity g p:ℝ)→
        (∫t:ℝ in {t:ℝ|T≤|t|},‖scaledBoundaryFourier P g p L x t‖)≤C*Real.exp (-c*T^2):=by
  obtain ⟨c,C,hc,hC,hTail⟩:=boundary_generating_fourier_tail_scaled P
  refine ⟨c,C,hc,hC,?_⟩
  intro g p hp hs hh L x hx T hT0 hT
  let σ:ℝ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
  have hhpos:0<(complexity g p:ℝ):=by exact_mod_cast (show 0<complexity g p by omega)
  have hv:0<euler Psi x:=mul_pos hx.1 (Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hσ:0<σ:=Real.sqrt_pos.mpr (mul_pos hhpos hv)
  unfold scaledBoundaryFourier
  rw[Analysis.scaledCenteredFourier_tail_change_variables (boundaryPGF P g p L x) _ _ _ hσ]
  exact hTail g p hp hs hh L x hx T hT0 hT
end WP.BoundaryConvolution
