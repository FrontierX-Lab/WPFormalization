import WPFormalization.Critical.ShortConfigurationRecordingEmbedded
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.LocalAtTarget
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.ShortConfiguration
open Set Metric Topology
open scoped Classical

/-- A partial equivalence on an open stratum has a continuous inverse when
its extension over a compact closure never sends boundary points into that
stratum. Endpoint identifications outside the stratum are allowed. -/
lemma _root_.PartialEquiv.continuousOn_symm_of_compact {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B]
    (e : PartialEquiv A B) (K : Set A) (hK : IsCompact K)
    (he : ContinuousOn e K) (hsub : e.source⊆K)
    (hpre : ∀x∈K,e x∈e.target→x∈e.source) :
    ContinuousOn e.symm e.target := by
  let f : K→B := fun x=>e x.val
  have hf : Continuous f := he.domRestrict
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hclosed : IsClosedMap f := hf.isClosedMap
  let F : (f ⁻¹' e.target)→e.target := e.target.restrictPreimage f
  have hF : Continuous F := hf.restrictPreimage
  have hFc : IsClosedMap F := hclosed.restrictPreimage e.target
  have hFb : Function.Bijective F := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply e.injOn
      · exact hpre _ x.val.property x.property
      · exact hpre _ y.val.property y.property
      · exact congrArg Subtype.val hxy
    · intro y
      refine ⟨⟨⟨e.symm y.val,hsub (e.map_target y.property)⟩,?_⟩,?_⟩
      · change e (e.symm y.val) ∈ e.target
        rw [e.right_inv y.property]
        exact y.property
      · apply Subtype.ext
        exact e.right_inv y.property
  let H := (Equiv.ofBijective F hFb).toHomeomorphOfContinuousClosed hF hFc
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hcont : Continuous (fun y:e.target=>(H.symm y).val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp H.symm.continuous)
  apply hcont.congr
  intro y
  apply e.injOn
  · exact hpre _ (H.symm y).val.property (H.symm y).property
  · exact e.map_target y.property
  · have hy := congrArg Subtype.val (H.apply_symm_apply y)
    exact hy.trans (e.right_inv y.property).symm

variable {X : Type u} [MetricSpace X] (N : EmbeddedNetwork.{u,0} X)

def edgeCoordinate (e : N.Edge) (z : Fin 1→ℝ) : ℝ :=
  N.start e+(z 0+1)/2*(N.finish e-N.start e)

def edgeCharacteristic (e : N.Edge) (z : Fin 1→ℝ) : X :=
  N.curve e (edgeCoordinate N e z)

lemma finOne_mem_ball (z : Fin 1→ℝ) :
    z∈ball (0 : Fin 1→ℝ) 1 ↔ -1<z 0 ∧ z 0<1 := by
  simp only [mem_ball_zero_iff, pi_norm_lt_iff (by norm_num : (0:ℝ)<1),
    Real.norm_eq_abs, abs_lt]
  constructor
  · intro h;exact h 0
  · intro h i; fin_cases i;exact h

lemma finOne_mem_closedBall (z : Fin 1→ℝ) :
    z∈closedBall (0 : Fin 1→ℝ) 1 ↔ -1≤z 0 ∧ z 0≤1 := by
  simp only [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1),
    Real.norm_eq_abs, abs_le]
  constructor
  · intro h;exact h 0
  · intro h i; fin_cases i;exact h

lemma edgeCoordinate_mem_Ioo (e : N.Edge) (z : Fin 1→ℝ) :
    edgeCoordinate N e z∈Ioo (N.start e) (N.finish e) ↔ z∈ball 0 1 := by
  rw [finOne_mem_ball]
  have hd := N.interval_pos e
  have hd' : 0<N.finish e-N.start e := sub_pos.mpr hd
  constructor
  · intro h
    constructor
    · have hh : 0<(z 0+1)/2*(N.finish e-N.start e) := by
        dsimp [edgeCoordinate] at h
        linarith [h.1]
      have := (mul_pos_iff_of_pos_right hd').mp hh
      linarith
    · have hh : (z 0+1)/2*(N.finish e-N.start e)<1*(N.finish e-N.start e) := by
        dsimp [edgeCoordinate] at h
        linarith [h.2]
      have := (mul_lt_mul_iff_left₀ hd').mp hh
      linarith
  · intro h
    constructor
    · have hh := mul_pos (by linarith : 0<(z 0+1)/2) hd'
      dsimp [edgeCoordinate];linarith
    · have hh := (mul_lt_mul_iff_left₀ hd').mpr (show (z 0+1)/2<1 by linarith)
      dsimp [edgeCoordinate];linarith

lemma edgeCoordinate_mem_Icc (e : N.Edge) (z : Fin 1→ℝ) :
    edgeCoordinate N e z∈Icc (N.start e) (N.finish e) ↔ z∈closedBall 0 1 := by
  rw [finOne_mem_closedBall]
  have hd := N.interval_pos e
  have hd' : 0<N.finish e-N.start e := sub_pos.mpr hd
  constructor
  · intro h
    constructor
    · have hh : 0≤(z 0+1)/2*(N.finish e-N.start e) := by
        dsimp [edgeCoordinate] at h;linarith [h.1]
      have := (mul_nonneg_iff_of_pos_right hd').mp hh
      linarith
    · have hh : (z 0+1)/2*(N.finish e-N.start e)≤1*(N.finish e-N.start e) := by
        dsimp [edgeCoordinate] at h;linarith [h.2]
      have := (mul_le_mul_iff_left₀ hd').mp hh
      linarith
  · intro h
    constructor
    · have hh := mul_nonneg (by linarith : 0≤(z 0+1)/2) (le_of_lt hd')
      dsimp [edgeCoordinate];linarith
    · have hh := (mul_le_mul_iff_left₀ hd').mpr (show (z 0+1)/2≤1 by linarith)
      dsimp [edgeCoordinate];linarith

lemma edgeCoordinate_injective (e : N.Edge) : Function.Injective (edgeCoordinate N e) := by
  intro z w h
  have hd : N.finish e-N.start e≠0 := ne_of_gt (sub_pos.mpr (N.interval_pos e))
  have heq : z 0*(N.finish e-N.start e)=w 0*(N.finish e-N.start e) := by
    dsimp [edgeCoordinate] at h
    nlinarith only [h]
  have hz := mul_right_cancel₀ hd heq
  funext i
  fin_cases i
  exact hz

lemma edgeCharacteristic_injOn (e : N.Edge) :
    InjOn (edgeCharacteristic N e) (ball 0 1) := by
  intro z hz w hw h
  apply edgeCoordinate_injective N e
  exact N.interval_injective e (Ioo_subset_Ico_self ((edgeCoordinate_mem_Ioo N e z).mpr hz))
    (Ioo_subset_Ico_self ((edgeCoordinate_mem_Ioo N e w).mpr hw)) h

lemma edgeCharacteristic_continuous (e : N.Edge) : Continuous (edgeCharacteristic N e) := by
  apply (N.lipschitz e).continuous.comp
  change Continuous (fun z : Fin 1→ℝ => N.start e+(z 0+1)/2*(N.finish e-N.start e))
  fun_prop

def edgeCellEquiv (e : N.Edge) : PartialEquiv (Fin 1→ℝ) X :=
  (edgeCharacteristic_injOn N e).toPartialEquiv (edgeCharacteristic N e) (ball 0 1)

@[simp] lemma edgeCellEquiv_source (e : N.Edge) : (edgeCellEquiv N e).source=ball 0 1 := rfl
@[simp] lemma edgeCellEquiv_apply (e : N.Edge) (z : Fin 1→ℝ) :
    edgeCellEquiv N e z=edgeCharacteristic N e z := rfl

lemma edgeCoordinate_surjective (e : N.Edge) (t : ℝ) :
    ∃z:Fin 1→ℝ,edgeCoordinate N e z=t := by
  refine ⟨fun _=>2*(t-N.start e)/(N.finish e-N.start e)-1,?_⟩
  have hd : N.finish e-N.start e≠0 := ne_of_gt (sub_pos.mpr (N.interval_pos e))
  dsimp [edgeCoordinate]
  field_simp
  ring

lemma edgeCellEquiv_image_ball (e : N.Edge) :
    edgeCellEquiv N e '' ball 0 1=N.curve e '' Ioo (N.start e) (N.finish e) := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨edgeCoordinate N e z,(edgeCoordinate_mem_Ioo N e z).mpr hz,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨z,hz⟩ := edgeCoordinate_surjective N e t
    refine ⟨z,(edgeCoordinate_mem_Ioo N e z).mp (hz ▸ ht),?_⟩
    change N.curve e (edgeCoordinate N e z)=N.curve e t
    rw [hz]

lemma edgeCellEquiv_image_closedBall (e : N.Edge) :
    edgeCellEquiv N e '' closedBall 0 1=N.curve e '' Icc (N.start e) (N.finish e) := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨edgeCoordinate N e z,(edgeCoordinate_mem_Icc N e z).mpr hz,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨z,hz⟩ := edgeCoordinate_surjective N e t
    refine ⟨z,(edgeCoordinate_mem_Icc N e z).mp (hz ▸ ht),?_⟩
    change N.curve e (edgeCoordinate N e z)=N.curve e t
    rw [hz]

lemma edgeCellEquiv_target (e : N.Edge) :
    (edgeCellEquiv N e).target=N.curve e '' Ioo (N.start e) (N.finish e) :=
  edgeCellEquiv_image_ball N e

lemma edgeCellEquiv_continuousOn_symm (e : N.Edge) :
    ContinuousOn (edgeCellEquiv N e).symm (edgeCellEquiv N e).target := by
  apply PartialEquiv.continuousOn_symm_of_compact (edgeCellEquiv N e) (closedBall 0 1)
    (isCompact_closedBall 0 1) (edgeCharacteristic_continuous N e).continuousOn
  · exact ball_subset_closedBall
  · intro z hz ht
    rw [edgeCellEquiv_target] at ht
    have hn : edgeCellEquiv N e z∉N.vertices := by
      intro hv
      exact Set.disjoint_left.mp (N.interior_avoids e) ht hv
    have hc := (edgeCoordinate_mem_Icc N e z).mpr hz
    have ha : edgeCoordinate N e z≠N.start e := by
      intro he
      apply hn
      change N.curve e (edgeCoordinate N e z)∈N.vertices
      rw [he]
      exact N.start_vertex e
    have hb : edgeCoordinate N e z≠N.finish e := by
      intro he
      apply hn
      change N.curve e (edgeCoordinate N e z)∈N.vertices
      rw [he]
      exact N.finish_vertex e
    exact (edgeCoordinate_mem_Ioo N e z).mp ⟨lt_of_le_of_ne hc.1 ha.symm,lt_of_le_of_ne hc.2 hb⟩

lemma edgeCellEquiv_sphere_maps_vertices (e : N.Edge) :
    MapsTo (edgeCellEquiv N e) (sphere 0 1) (N.vertices : Set X) := by
  intro z hz
  have hc := (edgeCoordinate_mem_Icc N e z).mpr (sphere_subset_closedBall hz)
  have hn : z∉ball (0 : Fin 1→ℝ) 1 := by
    intro hh
    have he : ‖z‖=1 := by simpa only [mem_sphere,dist_zero_right] using hz
    have hl : ‖z‖<1 := by simpa only [mem_ball,dist_zero_right] using hh
    linarith
  have hb : edgeCoordinate N e z=N.start e ∨ edgeCoordinate N e z=N.finish e := by
    by_contra h
    push Not at h
    apply hn
    exact (edgeCoordinate_mem_Ioo N e z).mp ⟨lt_of_le_of_ne hc.1 h.1.symm,lt_of_le_of_ne hc.2 h.2⟩
  change N.curve e (edgeCoordinate N e z)∈N.vertices
  rcases hb with h|h
  · rw [h];exact N.start_vertex e
  · rw [h];exact N.finish_vertex e

/-- Restrict a partial equivalence to a subtype containing its target. Its
value outside that subtype is irrelevant to the partial equivalence. -/
def _root_.PartialEquiv.codomainSubtype {A : Type*} {B : Type*} (e : PartialEquiv A B)
    (S : Set B) (p : S) (ht : e.target⊆S) : PartialEquiv A S where
  toFun a := if h:e a∈S then ⟨e a,h⟩ else p
  invFun b := e.symm b.val
  source := e.source
  target := Subtype.val ⁻¹' e.target
  map_source' a ha := by
    rw [dite_eq_left (ht (e.map_source ha))]
    exact e.map_source ha
  map_target' b hb := e.map_target hb
  left_inv' a ha := by
    rw [dite_eq_left (ht (e.map_source ha))]
    exact e.left_inv ha
  right_inv' b hb := by
    apply Subtype.ext
    have he := e.right_inv hb
    rw [dite_eq_left (show e (e.symm b.val)∈S by rw [he];exact b.property)]
    exact he

lemma _root_.PartialEquiv.codomainSubtype_coe {A : Type*} {B : Type*} (e : PartialEquiv A B)
    (S : Set B) (p : S) (ht : e.target⊆S) {a : A} (ha : e a∈S) :
    ((e.codomainSubtype S p ht a : S) : B)=e a := by
  simp only [PartialEquiv.codomainSubtype,PartialEquiv.coe_mk,dite_eq_left ha]

lemma _root_.PartialEquiv.codomainSubtype_image {A : Type*} {B : Type*} (e : PartialEquiv A B)
    (S : Set B) (p : S) (ht : e.target⊆S) (K : Set A) (hK : e '' K⊆S) :
    e.codomainSubtype S p ht '' K=Subtype.val ⁻¹' (e '' K) := by
  ext b
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a,ha,(e.codomainSubtype_coe S p ht (hK ⟨a,ha,rfl⟩)).symm⟩
  · rintro ⟨a,ha,he⟩
    refine ⟨a,ha,?_⟩
    apply Subtype.ext
    exact (e.codomainSubtype_coe S p ht (hK ⟨a,ha,rfl⟩)).trans he

lemma _root_.PartialEquiv.codomainSubtype_continuousOn {A : Type*} {B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (e : PartialEquiv A B)
    (S : Set B) (p : S) (ht : e.target⊆S) (K : Set A)
    (hK : e '' K⊆S) (he : ContinuousOn e K) :
    ContinuousOn (e.codomainSubtype S p ht) K := by
  apply IsInducing.subtypeVal.continuousOn_iff.mpr
  apply he.congr
  intro a ha
  exact e.codomainSubtype_coe S p ht (hK ⟨a,ha,rfl⟩)

lemma _root_.PartialEquiv.codomainSubtype_continuousOn_symm {A : Type*} {B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (e : PartialEquiv A B)
    (S : Set B) (p : S) (ht : e.target⊆S)
    (he : ContinuousOn e.symm e.target) :
    ContinuousOn (e.codomainSubtype S p ht).symm (e.codomainSubtype S p ht).target :=
  he.comp continuous_subtype_val.continuousOn (fun _ hx=>hx)

lemma EmbeddedNetwork.vertex_mem_support (v : X) (hv : v∈N.vertices) : v∈N.support := by
  obtain ⟨e,he⟩ := N.vertices_covered v hv
  refine mem_iUnion.mpr ⟨e,N.start e,?_,he⟩
  exact ⟨le_rfl,(N.interval_pos e).le⟩

lemma edgeCellEquiv_closed_image_subset_support (e : N.Edge) :
    edgeCellEquiv N e '' closedBall 0 1⊆N.support := by
  rw [edgeCellEquiv_image_closedBall]
  exact subset_iUnion (fun f=>N.curve f '' Icc (N.start f) (N.finish f)) e

lemma edgeCellEquiv_target_subset_support (e : N.Edge) : (edgeCellEquiv N e).target⊆N.support := by
  rw [edgeCellEquiv_target]
  exact (image_mono Ioo_subset_Icc_self).trans (subset_iUnion
    (fun f=>N.curve f '' Icc (N.start f) (N.finish f)) e)

def edgeSupportCell (e : N.Edge) : PartialEquiv (Fin 1→ℝ) N.support :=
  (edgeCellEquiv N e).codomainSubtype N.support
    ⟨N.curve e (N.start e),N.vertex_mem_support _ (N.start_vertex e)⟩
    (edgeCellEquiv_target_subset_support N e)

lemma edgeSupportCell_image_ball (e : N.Edge) :
    edgeSupportCell N e '' ball 0 1=Subtype.val ⁻¹' (N.curve e '' Ioo (N.start e) (N.finish e)) := by
  rw [edgeSupportCell,PartialEquiv.codomainSubtype_image]
  · rw [edgeCellEquiv_image_ball]
  · exact (image_mono ball_subset_closedBall).trans (edgeCellEquiv_closed_image_subset_support N e)

lemma edgeSupportCell_image_closedBall (e : N.Edge) :
    edgeSupportCell N e '' closedBall 0 1=Subtype.val ⁻¹' (N.curve e '' Icc (N.start e) (N.finish e)) := by
  rw [edgeSupportCell,PartialEquiv.codomainSubtype_image]
  · rw [edgeCellEquiv_image_closedBall]
  · exact edgeCellEquiv_closed_image_subset_support N e

lemma edgeSupportCell_continuousOn (e : N.Edge) : ContinuousOn (edgeSupportCell N e) (closedBall 0 1) :=
  (edgeCellEquiv N e).codomainSubtype_continuousOn _ _ _ _
    (edgeCellEquiv_closed_image_subset_support N e) (edgeCharacteristic_continuous N e).continuousOn

lemma edgeSupportCell_continuousOn_symm (e : N.Edge) :
    ContinuousOn (edgeSupportCell N e).symm (edgeSupportCell N e).target :=
  (edgeCellEquiv N e).codomainSubtype_continuousOn_symm _ _ _ (edgeCellEquiv_continuousOn_symm N e)

/-- Actual vertices, retaining their given points in the metric space. -/
def NetworkVertices := {v : X // v∈N.vertices}

def supportVertex (v : NetworkVertices N) : N.support :=
  ⟨v.val,N.vertex_mem_support v.val v.property⟩

def vertexSupportCell (v : NetworkVertices N) : PartialEquiv (Fin 0→ℝ) N.support :=
  (show InjOn (fun _ : Fin 0→ℝ=>supportVertex N v) (ball 0 1) from
    fun _ _ _ _ _=>Subsingleton.elim _ _).toPartialEquiv
      (fun _=>supportVertex N v) (ball 0 1)

lemma vertexSupportCell_image (v : NetworkVertices N) (K : Set (Fin 0→ℝ)) (hK : K.Nonempty) :
    vertexSupportCell N v '' K={supportVertex N v} :=
  by
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩;rfl
    · intro hp
      obtain ⟨z,hz⟩ := hK
      exact ⟨z,hz,hp.symm⟩

lemma vertexSupportCell_continuousOn (v : NetworkVertices N) :
    ContinuousOn (vertexSupportCell N v) (closedBall 0 1) := continuous_const.continuousOn

lemma vertexSupportCell_continuousOn_symm (v : NetworkVertices N) :
    ContinuousOn (vertexSupportCell N v).symm (vertexSupportCell N v).target := by
  have he : ⇑(vertexSupportCell N v).symm=(fun _=> (0:Fin 0→ℝ)) := by
    funext p
    exact Subsingleton.elim _ _
  rw [he]
  exact continuous_const.continuousOn

lemma edgeSupportCell_coe (e : N.Edge) {z : Fin 1→ℝ} (hz : z∈closedBall 0 1) :
    (edgeSupportCell N e z).val=edgeCellEquiv N e z :=
  (edgeCellEquiv N e).codomainSubtype_coe _ _ _
    (edgeCellEquiv_closed_image_subset_support N e ⟨z,hz,rfl⟩)

instance : Fintype (NetworkVertices N) := inferInstanceAs (Fintype {v : X // v∈N.vertices})

/-- The zero-cells are the actual vertices, the one-cells the actual edges,
and there are no higher-dimensional cells. -/
def NetworkCells : ℕ→Type u
  | 0 => NetworkVertices N
  | 1 => ULift.{u} N.Edge
  | _+2 => PEmpty.{u+1}

instance networkCells_finite (n : ℕ) : Finite (NetworkCells N n) := by
  cases n with
  | zero => exact inferInstanceAs (Finite (NetworkVertices N))
  | succ n => cases n with
    | zero => exact inferInstanceAs (Finite (ULift.{u} N.Edge))
    | succ n => exact inferInstanceAs (Finite PEmpty)

def networkCellMap : (n : ℕ)→NetworkCells N n→PartialEquiv (Fin n→ℝ) N.support
  | 0,v => vertexSupportCell N v
  | 1,e => edgeSupportCell N e.down
  | _+2,e => e.elim

lemma networkCells_high_empty (n : ℕ) (hn : 2≤n) : IsEmpty (NetworkCells N n) := by
  cases n with
  | zero => omega
  | succ n => cases n with
    | zero => omega
    | succ n => exact inferInstanceAs (IsEmpty PEmpty)

lemma networkCells_eventually_empty : ∀ᶠ n in Filter.atTop,IsEmpty (NetworkCells N n) :=
  Filter.eventually_atTop.mpr ⟨2,networkCells_high_empty N⟩

lemma networkCellMap_source (n : ℕ) (c : NetworkCells N n) :
    (networkCellMap N n c).source=ball 0 1 := by
  cases n with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n => exact c.elim

lemma networkCellMap_continuousOn (n : ℕ) (c : NetworkCells N n) :
    ContinuousOn (networkCellMap N n c) (closedBall 0 1) := by
  cases n with
  | zero => exact vertexSupportCell_continuousOn N c
  | succ n => cases n with
    | zero => exact edgeSupportCell_continuousOn N c.down
    | succ n => exact c.elim

lemma networkCellMap_continuousOn_symm (n : ℕ) (c : NetworkCells N n) :
    ContinuousOn (networkCellMap N n c).symm (networkCellMap N n c).target := by
  cases n with
  | zero => exact vertexSupportCell_continuousOn_symm N c
  | succ n => cases n with
    | zero => exact edgeSupportCell_continuousOn_symm N c.down
    | succ n => exact c.elim

lemma networkCellMap_pairwiseDisjoint :
    (univ : Set (Σn,NetworkCells N n)).PairwiseDisjoint
      (fun nc=>networkCellMap N nc.1 nc.2 '' ball 0 1) := by
  rintro ⟨m,v⟩ _ ⟨n,w⟩ _ hne
  cases m with
  | zero =>
    cases n with
    | zero =>
      change Disjoint (vertexSupportCell N v '' ball 0 1) (vertexSupportCell N w '' ball 0 1)
      rw [vertexSupportCell_image N v _ ⟨0,by simp⟩,
        vertexSupportCell_image N w _ ⟨0,by simp⟩]
      apply Set.disjoint_left.mpr
      intro p hp hq
      have hp := Set.mem_singleton_iff.mp hp
      have hq := Set.mem_singleton_iff.mp hq
      have heq : v=w := Subtype.ext (congrArg (fun q : N.support=>q.val) (hp.symm.trans hq))
      apply hne
      subst w
      rfl
    | succ n => cases n with
      | zero =>
        change Disjoint (vertexSupportCell N v '' ball 0 1) (edgeSupportCell N w.down '' ball 0 1)
        rw [vertexSupportCell_image N v _ ⟨0,by simp⟩,edgeSupportCell_image_ball]
        apply Set.disjoint_left.mpr
        intro p hp hq
        have hp := Set.mem_singleton_iff.mp hp
        have hv : p.val∈N.vertices := by rw [hp];exact v.property
        exact Set.disjoint_left.mp (N.interior_avoids w.down) hq hv
      | succ n => exact w.elim
  | succ m => cases m with
    | zero =>
      cases n with
      | zero =>
        change Disjoint (edgeSupportCell N v.down '' ball 0 1) (vertexSupportCell N w '' ball 0 1)
        rw [edgeSupportCell_image_ball,vertexSupportCell_image N w _ ⟨0,by simp⟩]
        apply Set.disjoint_left.mpr
        intro p hp hq
        have hq := Set.mem_singleton_iff.mp hq
        have hv : p.val∈N.vertices := by rw [hq];exact w.property
        exact Set.disjoint_left.mp (N.interior_avoids v.down) hp hv
      | succ n => cases n with
        | zero =>
          change Disjoint (edgeSupportCell N v.down '' ball 0 1) (edgeSupportCell N w.down '' ball 0 1)
          rw [edgeSupportCell_image_ball,edgeSupportCell_image_ball]
          have hed : v.down≠w.down := by
            intro he
            apply hne
            have hvw : v=w := ULift.ext _ _ he
            subst w
            rfl
          apply Set.disjoint_left.mpr
          intro p hp hq
          exact Set.disjoint_left.mp (N.interiors_disjoint _ _ hed) hp hq
        | succ n => exact w.elim
    | succ m => exact v.elim

lemma networkCellMap_mapsTo (n : ℕ) (c : NetworkCells N n) :
    MapsTo (networkCellMap N n c) (sphere 0 1)
      (⋃m,⋃(_ : m<n),⋃j:NetworkCells N m,networkCellMap N m j '' closedBall 0 1) := by
  cases n with
  | zero =>
    intro z hz
    have he : ‖z‖=1 := by simpa only [mem_sphere,dist_zero_right] using hz
    have hz0 : z=(0:Fin 0→ℝ) := Subsingleton.elim _ _
    rw [hz0,norm_zero] at he
    norm_num at he
  | succ n => cases n with
    | zero =>
      intro z hz
      let p := edgeSupportCell N c.down z
      have hv : p.val∈N.vertices := by
        change (edgeSupportCell N c.down z).val∈N.vertices
        rw [edgeSupportCell_coe N c.down (sphere_subset_closedBall hz)]
        exact edgeCellEquiv_sphere_maps_vertices N c.down hz
      let v : NetworkVertices N := ⟨p.val,hv⟩
      refine mem_iUnion.mpr ⟨0,mem_iUnion.mpr ⟨by decide,mem_iUnion.mpr ⟨v,?_⟩⟩⟩
      change p∈vertexSupportCell N v '' closedBall 0 1
      rw [vertexSupportCell_image N v _ ⟨0,by simp⟩]
      exact Subtype.ext rfl
    | succ n => exact c.elim

lemma networkCellMap_union :
    (⋃n,⋃c:NetworkCells N n,networkCellMap N n c '' closedBall 0 1)=(univ : Set N.support) := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨e,t,ht,he⟩ := mem_iUnion.mp p.property
  refine mem_iUnion.mpr ⟨1,mem_iUnion.mpr ⟨ULift.up e,?_⟩⟩
  change p∈edgeSupportCell N e '' closedBall 0 1
  rw [edgeSupportCell_image_closedBall]
  exact ⟨t,ht,he⟩

/-- A finite one-dimensional CW structure on the actual metric support.
The characteristic maps agree on each closed unit ball with the actual
vertex point or affine edge arc; endpoint identifications are retained. -/
@[instance_reducible] def networkCW : CWComplex (univ : Set N.support) :=
  CWComplex.mkFinite univ (NetworkCells N) (networkCellMap N)
    (networkCells_eventually_empty N) (networkCells_finite N)
    (networkCellMap_source N) (networkCellMap_continuousOn N)
    (networkCellMap_continuousOn_symm N) (networkCellMap_pairwiseDisjoint N)
    (networkCellMap_mapsTo N) (networkCellMap_union N)

lemma networkCW_finite : letI := networkCW N
    CWComplex.Finite (univ : Set N.support) := by
  let := networkCW N
  exact {
    eventually_isEmpty_cell := networkCells_eventually_empty N
    finite_cell := networkCells_finite N }

def networkCW_zero_cells_equiv : letI := networkCW N
    Topology.RelCWComplex.cell (univ : Set N.support) 0 ≃ NetworkVertices N :=
  Equiv.refl _

def networkCW_one_cells_equiv : letI := networkCW N
    Topology.RelCWComplex.cell (univ : Set N.support) 1 ≃ N.Edge :=
  Equiv.ulift

lemma networkCW_zero_cells_card : letI := networkCW N
    Nat.card (Topology.RelCWComplex.cell (univ : Set N.support) 0)=N.vertices.card := by
  change Nat.card (NetworkVertices N)=N.vertices.card
  simp [NetworkVertices,Nat.card_eq_fintype_card]

lemma networkCW_one_cells_card : letI := networkCW N
    Nat.card (Topology.RelCWComplex.cell (univ : Set N.support) 1)=Nat.card N.Edge := by
  change Nat.card (ULift.{u} N.Edge)=Nat.card N.Edge
  exact Nat.card_congr Equiv.ulift

lemma networkCW_high_cells_empty (n : ℕ) (hn : 2≤n) : letI := networkCW N
    IsEmpty (Topology.RelCWComplex.cell (univ : Set N.support) n) :=
  networkCells_high_empty N n hn

end WP.Critical.ShortConfiguration
