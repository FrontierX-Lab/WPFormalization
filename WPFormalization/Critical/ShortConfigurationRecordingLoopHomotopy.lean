import WPFormalization.External.ShortLoopStraighteningGeometry
import WPFormalization.External.ShortRegularNeighborhoodGeometry
/- Actual loop homotopy operations and the regular-neighborhood boundary
retraction. The frontier loop is genuinely homotopic, in the SAME surface,
to the actual dart boundary walk. No small frontier metric length, filling,
straightened-side identification or recording property is a premise. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w
namespace WP.Critical.ShortConfiguration
open Set WP.External.ShortLoopStraighteningGeometry
open WP.External.ShortRegularNeighborhoodGeometry

namespace ClosedLoop
variable {X:Type u} [TopologicalSpace X] {Y:Type v} [TopologicalSpace Y]

lemma ext_map {f g:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X} (he:f.map=g.map) : f=g := by
  cases f
  cases g
  cases he
  rfl

lemma reverse_reverse (f:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X) : f.reverse.reverse=f := by
  apply ext_map
  ext t
  change f.map ⟨1-(1-(t:ℝ)),_⟩=f.map t
  congr 1
  apply Subtype.ext
  ring

lemma homotopy_refl (f:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X) : f.FreelyHomotopic f :=
  ⟨ContinuousMap.HomotopyWith.refl _ f.closed⟩

lemma homotopy_symm {f g:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X}
    (h:f.FreelyHomotopic g) : g.FreelyHomotopic f := h.map (·.symm)

lemma homotopy_trans {f g h:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X}
    (hfg:f.FreelyHomotopic g) (hgh:g.FreelyHomotopic h) : f.FreelyHomotopic h :=
  hfg.map2 (·.trans ·) hgh

lemma homotopy_reverse {f g:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X}
    (h:f.FreelyHomotopic g) : f.reverse.FreelyHomotopic g.reverse := by
  rcases h with ⟨H⟩
  let σ:C(unitInterval,unitInterval):=⟨fun t=>⟨1-(t:ℝ),by constructor <;> linarith [t.property.1,t.property.2]⟩,
    by fun_prop⟩
  refine ⟨{toHomotopy:=H.toHomotopy.compContinuousMap σ,prop':=?_}⟩
  intro t
  have ht:=H.prop t
  change H (t,0)=H (t,1) at ht
  change H (t,σ 0)=H (t,σ 1)
  simpa [σ] using ht.symm

lemma unoriented_refl (f:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X) :
    f.UnorientedFreelyHomotopic f := Or.inl (homotopy_refl f)

lemma unoriented_trans {f g h:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X}
    (hfg:f.UnorientedFreelyHomotopic g) (hgh:g.UnorientedFreelyHomotopic h) :
    f.UnorientedFreelyHomotopic h := by
  rcases hfg with hfg|hfg
  · rcases hgh with hgh|hgh
    · exact Or.inl (homotopy_trans hfg hgh)
    · exact Or.inr (homotopy_trans hfg hgh)
  · rcases hgh with hgh|hgh
    · exact Or.inr (homotopy_trans hfg (homotopy_reverse hgh))
    · exact Or.inl (homotopy_trans hfg (by simpa [reverse_reverse] using homotopy_reverse hgh))

lemma unoriented_symm {f g:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X}
    (h:f.UnorientedFreelyHomotopic g) : g.UnorientedFreelyHomotopic f := by
  rcases h with h|h
  · exact Or.inl (homotopy_symm h)
  · exact Or.inr (by simpa [reverse_reverse] using homotopy_reverse (homotopy_symm h))

def postcompose (f:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X) (F:C(X,Y)) :
    WP.External.ShortLoopStraighteningGeometry.ClosedLoop Y where
  map:=F.comp f.map
  closed:=congrArg F f.closed

lemma homotopy_postcompose {f g:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X}
    (h:f.FreelyHomotopic g) (F:C(X,Y)) :
    (postcompose f F).FreelyHomotopic (postcompose g F) := by
  rcases h with ⟨H⟩
  refine ⟨{toHomotopy:=ContinuousMap.Homotopy.comp (.refl F) H.toHomotopy,prop':=?_}⟩
  intro t
  exact congrArg F (H.prop t)

end ClosedLoop

variable {X:Type u} [MetricSpace X] (N:EmbeddedNetwork.{u,v} X)

def NeighborhoodData.frontierLoop (D:NeighborhoodData N)
    (l:WP.External.ShortLoopStraighteningGeometry.ClosedLoop (BoundaryWalkSpace N D.rotation)) :
    WP.External.ShortLoopStraighteningGeometry.ClosedLoop X where
  map:=⟨fun t=>(D.boundaryHomeo (l.map t)).val.val,by fun_prop⟩
  closed:=congrArg (fun p=>(D.boundaryHomeo p).val.val) l.closed

def NeighborhoodData.walkLoop (D:NeighborhoodData N)
    (l:WP.External.ShortLoopStraighteningGeometry.ClosedLoop (BoundaryWalkSpace N D.rotation)) :
    WP.External.ShortLoopStraighteningGeometry.ClosedLoop X :=
  ClosedLoop.postcompose l (boundaryWalk N D.rotation)

lemma NeighborhoodData.frontier_homotopic_walk (D:NeighborhoodData N)
    (l:WP.External.ShortLoopStraighteningGeometry.ClosedLoop (BoundaryWalkSpace N D.rotation)) :
    (NeighborhoodData.frontierLoop N D l).FreelyHomotopic (NeighborhoodData.walkLoop N D l) := by
  rcases D.deformation with ⟨h⟩
  let F:C(unitInterval,D.region):=⟨fun t=>(D.boundaryHomeo (l.map t)).val,by fun_prop⟩
  refine ⟨{
    toHomotopy := {
      toFun := fun p => (h (p.1,F p.2)).val
      continuous_toFun := by fun_prop
      map_zero_left := ?_
      map_one_left := ?_ }
    prop' := ?_ }⟩
  · intro t
    simp [F,NeighborhoodData.frontierLoop]
  · intro t
    rw [ContinuousMap.HomotopyWith.apply_one]
    simpa [F,NeighborhoodData.walkLoop,ClosedLoop.postcompose,setInclusion,
      walkInSupport] using congrArg Subtype.val (D.boundary_retract (l.map t))
  · intro t
    change (h (t,F 0)).val=(h (t,F 1)).val
    have he:F 0=F 1:=congrArg (fun z=>(D.boundaryHomeo z).val) l.closed
    rw [he]

end WP.Critical.ShortConfiguration
