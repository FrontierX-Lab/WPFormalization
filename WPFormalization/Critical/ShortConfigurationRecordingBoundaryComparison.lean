import WPFormalization.Critical.ShortConfigurationRecordingBoundaryStraightening
import WPFormalization.Critical.ShortConfigurationRecordingLoopHomotopy
noncomputable section
set_option maxHeartbeats 0
universe u v w
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortLoopStraighteningGeometry
open scoped Classical ENNReal

variable (B:BorderedGeometry.{u,v}) (hcomplete:B.surface.domain=univ)
  (H:LoopStraighteningClassics B hcomplete)
  {ι:Type w} [Fintype ι] (f:ι→WP.External.ShortLoopStraighteningGeometry.ClosedLoop B.surface.Point)
  (hsimple:∀i,(f i).Simple) (hpos:∀i,(f i).PositiveHomotopyLength)

lemma straightenedLoop_length_le_comparison
    (g:ι→WP.External.ShortLoopStraighteningGeometry.ClosedLoop B.surface.Point)
    (hfg:∀i,(f i).UnorientedFreelyHomotopic (g i))
    (W:ι→ℝ) (hW:∀i,0≤W i) (hlen:∀i,(g i).length≤ENNReal.ofReal (W i)) (i:ι) :
    B.curves.length (straightenedLoop B hcomplete H f hsimple hpos i)≤W i := by
  apply (ENNReal.ofReal_le_ofReal_iff (hW i)).mp
  exact (H.length_minimal _ (g i) (ClosedLoop.unoriented_trans
    (straightenedLoop_class B hcomplete H f hsimple hpos i) (hfg i))).trans (hlen i)

lemma straightenedBoundary_length_le_comparison
    (g:ι→WP.External.ShortLoopStraighteningGeometry.ClosedLoop B.surface.Point)
    (hfg:∀i,(f i).UnorientedFreelyHomotopic (g i))
    (W:ι→ℝ) (hW:∀i,0≤W i) (hlen:∀i,(g i).length≤ENNReal.ofReal (W i)) :
    ∑γ∈straightenedBoundary B hcomplete H f hsimple hpos,B.curves.length γ≤∑i,W i := by
  let q:=straightenedLoop B hcomplete H f hsimple hpos
  have hnonneg:∀i:ι,0≤B.curves.length (q i):=fun i=>(B.curves.representative (q i)).period_pos.le
  calc
    _ ≤∑γ∈straightenedBoundary B hcomplete H f hsimple hpos,
        ∑i∈univ.filter (fun i=>q i=γ),B.curves.length (q i) := by
      apply Finset.sum_le_sum
      intro γ hγ
      obtain ⟨i,hi,he⟩:=Finset.mem_image.mp hγ
      rw [←he]
      exact Finset.single_le_sum (fun j hj=>hnonneg j) (by simp [q])
    _ =∑i,B.curves.length (q i) :=
      Finset.sum_fiberwise_of_maps_to (s:=univ)
        (t:=straightenedBoundary B hcomplete H f hsimple hpos) (g:=q)
        (fun i hi=>Finset.mem_image.mpr ⟨i,hi,rfl⟩) (fun i=>B.curves.length (q i))
    _ ≤∑i,W i:=Finset.sum_le_sum (fun i hi=>straightenedLoop_length_le_comparison
      B hcomplete H f hsimple hpos g hfg W hW hlen i)

end WP.Critical.ShortConfiguration
