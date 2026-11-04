import WPFormalization.Critical.ShortConfigurationRecordingNetwork
import WPFormalization.Critical.ShortConfigurationRecordingSubdivision
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.ShortConfiguration
open Set Finset
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open scoped Classical

variable (B : BorderedGeometry) (H : SegmentClassics B) {r : ℕ}
    (γ : Fin r→B.curves.Primitive) (hinj : Function.Injective γ)
    (hsimple : ∀i,SimpleTrace B (γ i)) (L : ℝ) (hL : 0<L)
    (hlength : ∀i,B.curves.length (γ i)≤L)

local notation "P" => breakpoints B H γ hinj hsimple L hL hlength
local notation "E" => NetworkEdges B H γ hinj hsimple L hL hlength

def arcStart (e : E) : ℝ := subdivisionStart (P e.1) e.2

def arcEnd (e : E) : ℝ := subdivisionEnd (B.curves.length (γ e.1)) (P e.1) e.2

def arcInterior (e : E) : Set B.surface.Point :=
  curveParam B (γ e.1) '' Ioo (arcStart B H γ hinj hsimple L hL hlength e)
    (arcEnd B H γ hinj hsimple L hL hlength e)

def arcTrace (e : E) : Set B.surface.Point :=
  curveParam B (γ e.1) '' Icc (arcStart B H γ hinj hsimple L hL hlength e)
    (arcEnd B H γ hinj hsimple L hL hlength e)

lemma arcStart_nonneg (e : E) : 0≤arcStart B H γ hinj hsimple L hL hlength e :=
  (breakpoints_mem_period B H γ hinj hsimple L hL hlength e.1
    (subdivision_start_mem (P e.1) e.2)).1

lemma arcStart_lt_end (e : E) :
    arcStart B H γ hinj hsimple L hL hlength e<arcEnd B H γ hinj hsimple L hL hlength e :=
  subdivision_start_lt_end _ _ (fun t ht=>(breakpoints_mem_period B H γ hinj hsimple L hL hlength e.1 ht).2) e.2

lemma arcEnd_le_period (e : E) :
    arcEnd B H γ hinj hsimple L hL hlength e≤B.curves.length (γ e.1) := by
  unfold arcEnd subdivisionEnd
  split_ifs with hnext
  · exact (breakpoints_mem_period B H γ hinj hsimple L hL hlength e.1
      ((P e.1).orderEmbOfFin_mem rfl _)).2.le
  · exact le_rfl

lemma arc_interior_parameter_period (e : E) {t : ℝ}
    (ht : t∈Ioo (arcStart B H γ hinj hsimple L hL hlength e)
      (arcEnd B H γ hinj hsimple L hL hlength e)) : t∈Ico 0 (B.curves.length (γ e.1)) :=
  ⟨(arcStart_nonneg B H γ hinj hsimple L hL hlength e).trans ht.1.le,
    ht.2.trans_le (arcEnd_le_period B H γ hinj hsimple L hL hlength e)⟩

lemma arcInterior_avoids_crossings (e : E) :
    Disjoint (arcInterior B H γ hinj hsimple L hL hlength e)
      (crossingVertices B H γ hinj hsimple L hL hlength : Set B.surface.Point) := by
  apply Set.disjoint_left.mpr
  intro p hp hv
  obtain ⟨t,ht,rfl⟩ := hp
  have hperiod := arc_interior_parameter_period B H γ hinj hsimple L hL hlength e ht
  have hparam : t∈crossingParameterSet B H γ hinj hsimple L hL hlength e.1 := ⟨hperiod,hv⟩
  have hbreak : t∈P e.1 := mem_insert_of_mem ((crossingParameterSet_finite_card B H γ hinj hsimple L hL hlength e.1).1.mem_toFinset.mpr hparam)
  exact subdivision_no_breakpoint_inside _ (P e.1) e.2 hbreak ht

lemma arcInteriors_injective (e f : E) {p : B.surface.Point}
    (he : p∈arcInterior B H γ hinj hsimple L hL hlength e)
    (hf : p∈arcInterior B H γ hinj hsimple L hL hlength f) : e=f := by
  obtain ⟨t,ht,hpt⟩ := he
  obtain ⟨u,hu,hpu⟩ := hf
  by_cases hi : e.1=f.1
  · rcases e with ⟨i,j⟩
    rcases f with ⟨i',j'⟩
    dsimp at hi
    subst i'
    have htu : t=u := hsimple i (arc_interior_parameter_period B H γ hinj hsimple L hL hlength ⟨i,j⟩ ht)
      (arc_interior_parameter_period B H γ hinj hsimple L hL hlength ⟨i,j'⟩ hu) (hpt.trans hpu.symm)
    subst u
    have hjj : j=j' := subdivision_interval_unique _ _ ⟨ht.1.le,ht.2⟩ ⟨hu.1.le,hu.2⟩
    subst j'
    rfl
  · have hv : p∈crossingVertices B H γ hinj hsimple L hL hlength :=
      (crossingVertices_mem B H γ hinj hsimple L hL hlength p).mpr
        ⟨e.1,f.1,hi,⟨_,⟨t,rfl⟩,hpt⟩,⟨_,⟨u,rfl⟩,hpu⟩⟩
    exact ((Set.disjoint_left.mp (arcInterior_avoids_crossings B H γ hinj hsimple L hL hlength e)) ⟨t,ht,hpt⟩ hv).elim

lemma network_arcs_cover (p : B.surface.Point) (hp : ∃i,p∈B.curves.trace (γ i)) :
    ∃e:E,p∈arcTrace B H γ hinj hsimple L hL hlength e := by
  obtain ⟨i,hi⟩ := hp
  obtain ⟨t,ht,hpt⟩ := trace_has_period_parameter B (γ i) p hi
  obtain ⟨j,hj⟩ := subdivision_covers _ (P i) (zero_mem_breakpoints B H γ hinj hsimple L hL hlength i) ht
  exact ⟨⟨i,j⟩,t,⟨hj.1,hj.2.le⟩,hpt⟩


def networkPoints : Finset B.surface.Point :=
  crossingVertices B H γ hinj hsimple L hL hlength∪univ.image (fun i=>curveParam B (γ i) 0)

lemma networkPoints_card_le :
    (networkPoints B H γ hinj hsimple L hL hlength).card≤
      r*r*(Nat.floor (L/segmentScale L)+1)^2+r := by
  unfold networkPoints
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add
    (crossingVertices_card_le B H γ hinj hsimple L hL hlength) ?_)
  exact (card_image_le).trans (by simp)

lemma breakpoint_point_mem_network (i : Fin r) {t : ℝ} (ht : t∈P i) :
    curveParam B (γ i) t∈networkPoints B H γ hinj hsimple L hL hlength := by
  rcases mem_insert.mp ht with ht|ht
  · rw [ht]
    exact mem_union_right _ (mem_image.mpr ⟨i,mem_univ i,rfl⟩)
  · exact mem_union_left _ (((crossingParameterSet_finite_card B H γ hinj hsimple L hL hlength i).1.mem_toFinset.mp ht).2)

lemma arcStart_point_mem_network (e : E) :
    curveParam B (γ e.1) (arcStart B H γ hinj hsimple L hL hlength e)∈
      networkPoints B H γ hinj hsimple L hL hlength :=
  breakpoint_point_mem_network B H γ hinj hsimple L hL hlength e.1 (subdivision_start_mem (P e.1) e.2)

lemma arcEnd_point_mem_network (e : E) :
    curveParam B (γ e.1) (arcEnd B H γ hinj hsimple L hL hlength e)∈
      networkPoints B H γ hinj hsimple L hL hlength := by
  unfold arcEnd subdivisionEnd
  split_ifs with hnext
  · exact breakpoint_point_mem_network B H γ hinj hsimple L hL hlength e.1
      ((P e.1).orderEmbOfFin_mem rfl _)
  · have he := curveParam_periodic B (γ e.1) 0
    rw [zero_add] at he
    rw [he]
    exact mem_union_right _ (mem_image.mpr ⟨e.1,mem_univ _,rfl⟩)

lemma arcInterior_avoids_network (e : E) :
    Disjoint (arcInterior B H γ hinj hsimple L hL hlength e)
      (networkPoints B H γ hinj hsimple L hL hlength : Set B.surface.Point) := by
  apply Set.disjoint_left.mpr
  intro p hp hv
  rcases mem_union.mp hv with hv|hv
  · exact (Set.disjoint_left.mp (arcInterior_avoids_crossings B H γ hinj hsimple L hL hlength e)) hp hv
  · obtain ⟨i,hi,hp0⟩ := mem_image.mp hv
    obtain ⟨t,ht,hpt⟩ := hp
    by_cases he : e.1=i
    · have hpperiod := arc_interior_parameter_period B H γ hinj hsimple L hL hlength e ht
      have hzperiod : 0∈Ico 0 (B.curves.length (γ e.1)) :=
        ⟨le_rfl,(B.curves.representative (γ e.1)).period_pos⟩
      have ht0 : t=0 := hsimple e.1 hpperiod hzperiod (by simpa only [he] using hpt.trans hp0.symm)
      have hstart := arcStart_nonneg B H γ hinj hsimple L hL hlength e
      linarith [ht.1]
    · have hcross : p∈crossingVertices B H γ hinj hsimple L hL hlength :=
        (crossingVertices_mem B H γ hinj hsimple L hL hlength p).mpr
          ⟨e.1,i,he,⟨_,⟨t,rfl⟩,hpt⟩,⟨_,⟨0,rfl⟩,hp0⟩⟩
      exact (Set.disjoint_left.mp (arcInterior_avoids_crossings B H γ hinj hsimple L hL hlength e)) ⟨t,ht,hpt⟩ hcross

lemma network_arc_support :
    (⋃e:E,arcTrace B H γ hinj hsimple L hL hlength e)=⋃i,B.curves.trace (γ i) := by
  ext p
  constructor
  · intro hp
    obtain ⟨e,⟨t,ht,hpt⟩⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨e.1,_,⟨t,rfl⟩,hpt⟩
  · intro hp
    exact mem_iUnion.mpr (network_arcs_cover B H γ hinj hsimple L hL hlength p (mem_iUnion.mp hp))

lemma curveParam_lipschitz (B : BorderedGeometry) (γ : B.curves.Primitive) :
    LipschitzWith 1 (curveParam B γ) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [NNReal.coe_one,one_mul]
  let a := B.curves.representative γ
  have hb : BddBelow (range (fun δ:B.surface.Γ=>dist (a.axis s) (δ.val (a.axis t)))) :=
    ⟨0,by rintro _ ⟨δ,rfl⟩;exact dist_nonneg⟩
  have hh := csInf_le hb (show dist (a.axis s) (a.axis t)∈range (fun δ:B.surface.Γ=>dist (a.axis s) (δ.val (a.axis t))) from ⟨1,by simp⟩)
  rw [←B.surface.quotient_distance _ (a.in_domain s) _ (a.in_domain t)] at hh
  change dist (B.surface.project (a.axis s)) (B.surface.project (a.axis t)) ≤ dist s t
  exact hh.trans_eq (a.isometry.dist_eq s t)

end WP.Critical.ShortConfiguration
