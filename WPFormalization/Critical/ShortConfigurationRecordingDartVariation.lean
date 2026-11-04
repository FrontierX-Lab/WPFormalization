import WPFormalization.Critical.ShortConfigurationRecordingLoopHomotopy
import WPFormalization.Critical.ShortConfigurationDartCounts
import WPFormalization.Critical.ShortConfigurationRecordingLoopLength
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.ShortConfiguration
open Set Finset
open scoped ENNReal
variable {X:Type u} [MetricSpace X] (N:EmbeddedNetwork.{u,v} X)

lemma dartParameter_variation (d:NetworkDart N) :
    eVariationOn (dartParameter N d) univ=ENNReal.ofReal (N.finish d.1-N.start d.1) := by
  have hI:Icc (0:unitInterval) 1=univ:=Set.eq_univ_of_forall (fun t=>⟨t.property.1,t.property.2⟩)
  rcases d with ⟨e,b⟩
  have he:0<N.finish e-N.start e:=sub_pos.mpr (N.interval_pos e)
  cases b
  · have hm:MonotoneOn (dartParameter N (e,false)) univ:=by
      intro a ha b hb hab
      have h:(0:ℝ)≤(b-a)*(N.finish e-N.start e):=mul_nonneg (sub_nonneg.mpr hab) he.le
      dsimp [dartParameter]
      nlinarith
    have hv:=hm.eVariationOn_eq (a:=0) (b:=1) (mem_univ _) (mem_univ _)
    simpa [hI,dartParameter,sub_eq_add_neg,add_comm] using hv
  · have hm:MonotoneOn (fun t=> -dartParameter N (e,true) t) univ:=by
      intro a ha b hb hab
      have h:(0:ℝ)≤(b-a)*(N.finish e-N.start e):=mul_nonneg (sub_nonneg.mpr hab) he.le
      dsimp [dartParameter]
      nlinarith
    have hv:=hm.eVariationOn_eq (a:=0) (b:=1) (mem_univ _) (mem_univ _)
    have hneg:eVariationOn (dartParameter N (e,true)) univ=
        eVariationOn (fun t=> -dartParameter N (e,true) t) univ:=by
      simp only [eVariationOn,edist_neg_neg]
    rw [hneg]
    simpa [hI,dartParameter,sub_eq_add_neg,add_comm] using hv

lemma dartPoint_variation_le (d:NetworkDart N) :
    eVariationOn (fun t:unitInterval=>dartPoint N (d,t)) univ≤
      ENNReal.ofReal (N.finish d.1-N.start d.1) := by
  have h:=(N.lipschitz d.1).lipschitzOnWith.comp_eVariationOn_le
    (g:=dartParameter N d) (s:=univ) (fun t ht=>mem_univ _)
  simpa [Function.comp_def,dartPoint,dartParameter_variation] using h

lemma finite_partition_variation_le (f:unitInterval→X) (m:ℕ)
    (E:ℕ→unitInterval) (hE:Monotone E) (hzero:E 0=0) (hend:E m=1)
    (W:Fin m→ℝ≥0∞)
    (hlocal:∀j:Fin m,eVariationOn f (Icc (E j.val) (E (j.val+1)))≤W j) :
    eVariationOn f univ≤∑j,W j := by
  have hI:Icc (0:unitInterval) 1=univ:=Set.eq_univ_of_forall (fun t=>⟨t.property.1,t.property.2⟩)
  calc
    _ =∑j∈Finset.range m,eVariationOn f (Icc (E j) (E (j+1))) := by
      rw [eVariationOn.sum' f hE,hzero,hend,hI]
    _ =∑j:Fin m,eVariationOn f (Icc (E j.val) (E (j.val+1))) :=
      (Fin.sum_univ_eq_sum_range _ m).symm
    _ ≤∑j,W j:=Finset.sum_le_sum (fun j hj=>hlocal j)

lemma actual_boundary_walk_variation_le (R:NetworkRotation N)
    (l:WP.External.ShortLoopStraighteningGeometry.ClosedLoop (BoundaryWalkSpace N R))
    (m:ℕ) (E:ℕ→unitInterval) (hE:Monotone E) (hzero:E 0=0) (hend:E m=1)
    (d:Fin m→NetworkDart N) (φ:Fin m→unitInterval→unitInterval)
    (hφ:∀j,Monotone (φ j))
    (himage:∀j,range (φ j)=Icc (E j.val) (E (j.val+1)))
    (hdart:∀j t,boundaryWalk N R (l.map (φ j t))=dartPoint N (d j,t)) :
    (ClosedLoop.postcompose l (boundaryWalk N R)).length≤
      ∑j,ENNReal.ofReal (N.finish (d j).1-N.start (d j).1) := by
  apply finite_partition_variation_le _ m E hE hzero hend
  intro j
  have hcomp:eVariationOn ((boundaryWalk N R ∘ l.map) ∘ φ j) univ=
      eVariationOn (boundaryWalk N R ∘ l.map) (Icc (E j.val) (E (j.val+1))) := by
    have hc:=eVariationOn.comp_eq_of_monotoneOn (boundaryWalk N R ∘ l.map) (φ j) ((hφ j).monotoneOn univ)
    simpa [image_univ,himage j] using hc
  have hf:((boundaryWalk N R ∘ l.map) ∘ φ j)=(fun t:unitInterval=>dartPoint N (d j,t)):=by
    funext t
    exact hdart j t
  exact hcomp.symm.le.trans ((congrArg (fun F=>eVariationOn F univ) hf).le.trans
    (dartPoint_variation_le N (d j)))
end WP.Critical.ShortConfiguration
