import WPFormalization.Volumes.RatioQCusp
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter
open scoped Topology

def boundarySaddle (g p q:ℕ):ℝ :=
  XR (densityY (2*(q:ℝ)/(complexity g p:ℝ)))

lemma boundarySaddle_spec (g p q:ℕ)(hg:2≤g)(hq:1≤q) :
    boundarySaddle g p q∈Ioo (0:ℝ) xCritical ∧
      (complexity g p:ℝ)*Psi (boundarySaddle g p q)=(q:ℝ) ∧
      inverseY (boundarySaddle g p q)=densityY (2*(q:ℝ)/(complexity g p:ℝ)) := by
  have hh:0<(complexity g p:ℝ):=by
    exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hqr:0<(q:ℝ):=by exact_mod_cast (show 0<q by omega)
  have hs:=Analysis.ratioQ_saddle_spec (complexity g p) q hh hqr
  dsimp only at hs
  have hY:=hs.1
  have hx:XR (densityY (2*(q:ℝ)/(complexity g p:ℝ)))∈Ioo (0:ℝ) xCritical:=by
    constructor
    · simpa only [XR_zero] using XR_strictMonoOn y₀_pos.le hY.2.le hY.1
    · exact XR_strictMonoOn hY.2.le (by simp) hY.2
  exact ⟨hx,hs.2,Analysis.inverseY_eq_of_root _ _ hY.2.le rfl⟩

lemma boundary_effective_density_eq (g p q:ℕ)(hg:2≤g) :
    2*(q:ℝ)/(complexity g p:ℝ) =
      2*(((q+p:ℕ):ℝ)-(p:ℝ))/(2*(g:ℝ)-2+p) := by
  have hc:(complexity g p:ℝ)=2*(g:ℝ)-2+p:=by
    unfold complexity
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hc]
  push_cast
  congr 1
  ring

end WP.BoundaryConvolution
