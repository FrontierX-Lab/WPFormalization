import WPFormalization.External.FiniteCyclicIntervalGeometry
import WPFormalization.Critical.ShortConfigurationDartCounts
import WPFormalization.External.ShortLoopStraighteningGeometry
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Homeomorph.Quotient

noncomputable section
set_option maxHeartbeats 0
universe u v



namespace WP.Critical.ShortConfiguration
open Set Finset
open WP.External.ShortLoopStraighteningGeometry
open scoped Classical

/-- The already defined LoopCircle is the actual standard additive circle. -/
def loopCircleHomeomorphAddCircle : LoopCircle ≃ₜ AddCircle (1:ℝ) := by
  letI : Fact (0<(1:ℝ)):=⟨by norm_num⟩
  let e : Icc (0:ℝ) (0+1)≃ₜ unitInterval :=
    { toEquiv :=
        { toFun := fun s=>⟨s.val,by simpa using s.property⟩
          invFun := fun t=>⟨t.val,by simpa using t.property⟩
          left_inv := fun _=>rfl
          right_inv := fun _=>rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have he : ∀s t : Icc (0:ℝ) (0+1),
      AddCircle.EndpointIdent (1:ℝ) 0 s t ↔ loopCircleEndpoint (e s) (e t) := by
    intro s t
    constructor
    · intro h
      cases h
      constructor <;> apply Subtype.ext <;> simp [e]
    · rintro ⟨hs,ht⟩
      have hs' : s=⟨0,by norm_num⟩ := Subtype.ext (by simpa [e] using congrArg (fun z : unitInterval => (z:ℝ)) hs)
      have ht' : t=⟨0+1,by norm_num⟩ := Subtype.ext (by simpa [e] using congrArg (fun z : unitInterval => (z:ℝ)) ht)
      subst s
      subst t
      exact AddCircle.EndpointIdent.mk
  exact ((AddCircle.homeoIccQuot (1:ℝ) 0).trans (Homeomorph.Quot.congr e he)).symm

@[simp] lemma loopCircleHomeomorphAddCircle_mk (t : unitInterval) :
    loopCircleHomeomorphAddCircle (Quot.mk _ t)=(t:ℝ) := rfl

lemma loopCircle_mk_injOn : Set.InjOn (Quot.mk loopCircleEndpoint)
    (Ico (0:unitInterval) 1) := by
  intro s hs t ht hst
  apply Subtype.ext
  have hh:=congrArg loopCircleHomeomorphAddCircle hst
  simp only [loopCircleHomeomorphAddCircle_mk] at hh
  letI : Fact (0<(1:ℝ)):=⟨by norm_num⟩
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (p:=(1:ℝ)) (a:=0) ?_ ?_).mp hh
  · exact ⟨s.property.1,by simpa only [zero_add] using (show (s:ℝ)<1 from hs.2)⟩
  · exact ⟨t.property.1,by simpa only [zero_add] using (show (t:ℝ)<1 from ht.2)⟩

variable {X : Type u} [MetricSpace X] (N : EmbeddedNetwork.{u,v} X) (R : NetworkRotation N)

instance boundaryCycle_topology : TopologicalSpace (R.BoundaryCycle N) := ⊥
instance boundaryCycle_discrete : DiscreteTopology (R.BoundaryCycle N) := ⟨rfl⟩

@[simp] lemma dartCycle_face (d : NetworkDart N) :
    R.dartCycle N (R.face N d)=R.dartCycle N d := by
  apply Quotient.sound
  exact (Equiv.Perm.sameCycle_apply_left).mpr (Equiv.Perm.SameCycle.refl _ _)

/-- Every glued endpoint stays within the same finite face cycle. -/
def boundaryWalkCycle : C(BoundaryWalkSpace N R,R.BoundaryCycle N) where
  toFun:=Quot.lift (fun p : NetworkDart N × unitInterval=>R.dartCycle N p.1) (by
    intro p q h
    rcases h with ⟨_,rfl⟩
    exact (dartCycle_face N R p.1).symm)
  continuous_toFun:=continuous_quot_lift _ (by
    exact continuous_of_discreteTopology.comp continuous_fst)

@[simp] lemma boundaryWalkCycle_mk (d : NetworkDart N) (t : unitInterval) :
    boundaryWalkCycle N R (Quot.mk _ (d,t))=R.dartCycle N d := rfl

/-- The actual cycle subspace of the original endpoint quotient. -/
abbrev BoundaryCycleSpace (c : R.BoundaryCycle N) :=
  {p : BoundaryWalkSpace N R // boundaryWalkCycle N R p=c}

lemma boundaryWalkCycle_surjective : Function.Surjective (boundaryWalkCycle N R) := by
  intro c
  induction c using Quotient.ind with
  | _ d=> exact ⟨Quot.mk _ (d,0),rfl⟩

lemma cycleDarts_nonempty (c : R.BoundaryCycle N) : (R.cycleDarts N c).Nonempty := by
  induction c using Quotient.ind with
  | _ d=> exact ⟨d,(R.mem_cycleDarts N _ _).mpr rfl⟩

lemma cycleDarts_card_pos (c : R.BoundaryCycle N) : 0<(R.cycleDarts N c).card :=
  Finset.card_pos.mpr (cycleDarts_nonempty N R c)

lemma face_isCycleOn (c : R.BoundaryCycle N) :
    (R.face N).IsCycleOn (R.cycleDarts N c : Set (NetworkDart N)) := by
  refine ⟨⟨?_,(R.face N).injective.injOn,?_⟩,?_⟩
  · intro d hd
    exact (R.mem_cycleDarts N c _).mpr ((dartCycle_face N R d).trans ((R.mem_cycleDarts N c _).mp hd))
  · intro d hd
    refine ⟨(R.face N).symm d,?_,by simp⟩
    apply (R.mem_cycleDarts N c _).mpr
    have h:=dartCycle_face N R ((R.face N).symm d)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans ((R.mem_cycleDarts N c _).mp hd)
  · intro d hd e he
    exact Quotient.exact (((R.mem_cycleDarts N c _).mp hd).trans
      ((R.mem_cycleDarts N c _).mp he).symm)

noncomputable def cycleDartRoot (c : R.BoundaryCycle N) : NetworkDart N :=
  Classical.choose (cycleDarts_nonempty N R c)

lemma cycleDartRoot_mem (c : R.BoundaryCycle N) :
    cycleDartRoot N R c∈R.cycleDarts N c :=
  Classical.choose_spec (cycleDarts_nonempty N R c)

/-- Enumerate one actual face cycle by successive actual face permutations. -/
noncomputable def cycleDartEquiv (c : R.BoundaryCycle N) :
    Fin (R.cycleDarts N c).card ≃ {d // d∈R.cycleDarts N c} :=
  Equiv.ofBijective (fun j=>⟨((R.face N)^j.val) (cycleDartRoot N R c),
    (face_isCycleOn N R c).1.mapsTo.perm_pow _ (cycleDartRoot_mem N R c)⟩) (by
    constructor
    · intro i j hij
      apply Fin.ext
      have hh:=((face_isCycleOn N R c).pow_apply_eq_pow_apply
        (cycleDartRoot_mem N R c)).mp (congrArg Subtype.val hij)
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using hh
    · intro d
      obtain ⟨j,hj,hjd⟩:=(face_isCycleOn N R c).exists_pow_eq
        (cycleDartRoot_mem N R c) d.property
      exact ⟨⟨j,hj⟩,Subtype.ext hjd⟩)

/-- Cyclic successor is defined also for one-dart cycles, so loops are preserved. -/
def cycleDartNext (c : R.BoundaryCycle N) (j : Fin (R.cycleDarts N c).card) :
    Fin (R.cycleDarts N c).card :=
  ⟨(j.val+1) % (R.cycleDarts N c).card,Nat.mod_lt _ (cycleDarts_card_pos N R c)⟩

lemma cycleDartEquiv_next (c : R.BoundaryCycle N)
    (j : Fin (R.cycleDarts N c).card) :
    (cycleDartEquiv N R c (cycleDartNext N R c j)).val =
      R.face N (cycleDartEquiv N R c j).val := by
  change ((R.face N)^((j.val+1) % (R.cycleDarts N c).card)) (cycleDartRoot N R c) =
    R.face N (((R.face N)^j.val) (cycleDartRoot N R c))
  rw [← Equiv.Perm.mul_apply,← pow_succ']
  apply ((face_isCycleOn N R c).pow_apply_eq_pow_apply (cycleDartRoot_mem N R c)).mpr
  exact Nat.mod_modEq _ _

def cyclePolygonRelation (c : R.BoundaryCycle N)
    (p q : Fin (R.cycleDarts N c).card × unitInterval) : Prop :=
  p.2=1 ∧ q=(cycleDartNext N R c p.1,0)

abbrev CyclePolygon (c : R.BoundaryCycle N) := Quot (cyclePolygonRelation N R c)

/-- Literal dart-segment map to the original boundary walk quotient. -/
def cyclePolygonMap (c : R.BoundaryCycle N) :
    C(CyclePolygon N R c,BoundaryWalkSpace N R) where
  toFun:=Quot.lift (fun p=>Quot.mk _ ((cycleDartEquiv N R c p.1).val,p.2)) (by
    rintro p q ⟨hp,rfl⟩
    apply Quot.sound
    refine ⟨hp,?_⟩
    simp only [cycleDartEquiv_next])
  continuous_toFun:=continuous_quot_lift _ (by
    have hd : Continuous (fun j : Fin (R.cycleDarts N c).card=>
      (cycleDartEquiv N R c j).val) := continuous_of_discreteTopology
    exact continuous_quot_mk.comp ((hd.comp continuous_fst).prodMk continuous_snd))

@[simp] lemma cyclePolygonMap_mk (c : R.BoundaryCycle N)
    (j : Fin (R.cycleDarts N c).card) (t : unitInterval) :
    cyclePolygonMap N R c (Quot.mk _ (j,t))=
      Quot.mk _ ((cycleDartEquiv N R c j).val,t) := rfl

lemma cyclePolygonMap_cycle (c : R.BoundaryCycle N) (z : CyclePolygon N R c) :
    boundaryWalkCycle N R (cyclePolygonMap N R c z)=c := by
  induction z using Quot.ind with
  | _ p=>exact (R.mem_cycleDarts N c _).mp (cycleDartEquiv N R c p.1).property

lemma cycleDartEquiv_symm_face (c : R.BoundaryCycle N)
    (d : {d // d∈R.cycleDarts N c}) (hd : R.face N d.val∈R.cycleDarts N c) :
    (cycleDartEquiv N R c).symm ⟨R.face N d.val,hd⟩=
      cycleDartNext N R c ((cycleDartEquiv N R c).symm d) := by
  apply (cycleDartEquiv N R c).injective
  apply Subtype.ext
  simp only [Equiv.apply_symm_apply,cycleDartEquiv_next]

/-- Extraction is constant off the chosen cycle, hence continuous on all darts. -/
def cyclePolygonExtract (c : R.BoundaryCycle N) :
    C(BoundaryWalkSpace N R,CyclePolygon N R c) where
  toFun:=Quot.lift
    (fun p : NetworkDart N × unitInterval=>
      if hd : p.1∈R.cycleDarts N c then
        Quot.mk _ ((cycleDartEquiv N R c).symm ⟨p.1,hd⟩,p.2)
      else Quot.mk _ (⟨0,cycleDarts_card_pos N R c⟩,0)) (by
      rintro p q ⟨hp,rfl⟩
      have heq : R.face N p.1∈R.cycleDarts N c ↔ p.1∈R.cycleDarts N c := by
        simp only [R.mem_cycleDarts,dartCycle_face]
      by_cases hd : p.1∈R.cycleDarts N c
      · have hd' :=heq.mpr hd
        simp only [dite_eq_left hd,dite_eq_left hd']
        apply Quot.sound
        refine ⟨hp,?_⟩
        rw [cycleDartEquiv_symm_face N R c ⟨p.1,hd⟩ hd']
      · have hd' :=not_congr heq |>.mpr hd
        simp only [dite_eq_right hd,dite_eq_right hd'])
  continuous_toFun:=continuous_quot_lift _ (by
    apply continuous_prod_of_discrete_left.mpr
    intro d
    by_cases hd : d∈R.cycleDarts N c
    · simp only [dite_eq_left hd]
      exact continuous_quot_mk.comp
        ((continuous_const (y:=(cycleDartEquiv N R c).symm ⟨d,hd⟩)).prodMk
          (continuous_id (X:=unitInterval)))
    · simp only [dite_eq_right hd]
      exact continuous_const)

@[simp] lemma cyclePolygonExtract_mk_of_mem (c : R.BoundaryCycle N)
    (d : NetworkDart N) (hd : d∈R.cycleDarts N c) (t : unitInterval) :
    cyclePolygonExtract N R c (Quot.mk _ (d,t))=
      Quot.mk _ ((cycleDartEquiv N R c).symm ⟨d,hd⟩,t) := by
  exact dite_eq_left hd

lemma cyclePolygonExtract_map (c : R.BoundaryCycle N) (z : CyclePolygon N R c) :
    cyclePolygonExtract N R c (cyclePolygonMap N R c z)=z := by
  induction z using Quot.ind with
  | _ p=>
      rcases p with ⟨j,t⟩
      rw [cyclePolygonMap_mk,
        cyclePolygonExtract_mk_of_mem N R c _ (cycleDartEquiv N R c j).property]
      change Quot.mk _ ((cycleDartEquiv N R c).symm (cycleDartEquiv N R c j),t)=_
      rw [Equiv.symm_apply_apply]

lemma cyclePolygonMap_extract (c : R.BoundaryCycle N) (z : BoundaryWalkSpace N R)
    (hz : boundaryWalkCycle N R z=c) :
    cyclePolygonMap N R c (cyclePolygonExtract N R c z)=z := by
  induction z using Quot.ind with
  | _ p=>
      have hp : p.1∈R.cycleDarts N c := (R.mem_cycleDarts N c _).mpr hz
      simp only [cyclePolygonExtract_mk_of_mem N R c p.1 hp,cyclePolygonMap_mk,
        Equiv.apply_symm_apply]
      rfl

/-- The polygon consists of exactly the corresponding actual boundary component. -/
def cyclePolygonHomeomorph (c : R.BoundaryCycle N) :
    CyclePolygon N R c ≃ₜ BoundaryCycleSpace N R c where
  toEquiv :=
    { toFun :=fun z=>⟨cyclePolygonMap N R c z,cyclePolygonMap_cycle N R c z⟩
      invFun :=fun z=>cyclePolygonExtract N R c z.val
      left_inv :=cyclePolygonExtract_map N R c
      right_inv :=fun z=>Subtype.ext (cyclePolygonMap_extract N R c z.val z.property) }
  continuous_toFun :=(cyclePolygonMap N R c).continuous.subtype_mk
    (cyclePolygonMap_cycle N R c)
  continuous_invFun :=(cyclePolygonExtract N R c).continuous.comp continuous_subtype_val

/-- Composition only: the sole classical parameter is generic polygon gluing. -/
def cycleCircleHomeomorph (C : WP.External.FiniteCyclicIntervalGeometry.Classics)
    (c : R.BoundaryCycle N) : LoopCircle ≃ₜ BoundaryCycleSpace N R c :=
  loopCircleHomeomorphAddCircle.trans
    ((Classical.choose (C.circle (R.cycleDarts N c).card (cycleDarts_card_pos N R c))).trans
      (cyclePolygonHomeomorph N R c))

/-- Parameterization of an actual cycle inside the original walk space. -/
def cycleCircleMap (C : WP.External.FiniteCyclicIntervalGeometry.Classics)
    (c : R.BoundaryCycle N) : C(LoopCircle,BoundaryWalkSpace N R) :=
  ⟨fun z=>(cycleCircleHomeomorph N R C c z).val,
    continuous_subtype_val.comp (cycleCircleHomeomorph N R C c).continuous⟩

lemma cycleCircleMap_injective (C : WP.External.FiniteCyclicIntervalGeometry.Classics)
    (c : R.BoundaryCycle N) : Function.Injective (cycleCircleMap N R C c) := by
  intro z w hzw
  apply (cycleCircleHomeomorph N R C c).injective
  exact Subtype.ext hzw

@[simp] lemma boundaryWalkCycle_cycleCircleMap
    (C : WP.External.FiniteCyclicIntervalGeometry.Classics)
    (c : R.BoundaryCycle N) (z : LoopCircle) :
    boundaryWalkCycle N R (cycleCircleMap N R C c z)=c :=
  (cycleCircleHomeomorph N R C c z).property

lemma cycleCircleMap_range (C : WP.External.FiniteCyclicIntervalGeometry.Classics)
    (c : R.BoundaryCycle N) :
    Set.range (cycleCircleMap N R C c)={z | boundaryWalkCycle N R z=c} := by
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    exact boundaryWalkCycle_cycleCircleMap N R C c w
  · intro hz
    obtain ⟨w,hw⟩:=(cycleCircleHomeomorph N R C c).surjective ⟨z,hz⟩
    exact ⟨w,congrArg Subtype.val hw⟩

lemma cycleCircleMap_ranges_disjoint (C : WP.External.FiniteCyclicIntervalGeometry.Classics)
    {c d : R.BoundaryCycle N} (hcd : c≠d) :
    Disjoint (Set.range (cycleCircleMap N R C c)) (Set.range (cycleCircleMap N R C d)) := by
  rw [cycleCircleMap_range,cycleCircleMap_range,Set.disjoint_left]
  intro z hc hd
  exact hcd (hc.symm.trans hd)

lemma cycleCircleMap_ranges_cover (C : WP.External.FiniteCyclicIntervalGeometry.Classics) :
    (⋃c,Set.range (cycleCircleMap N R C c))=Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  apply Set.mem_iUnion.mpr
  refine ⟨boundaryWalkCycle N R z,?_⟩
  rw [cycleCircleMap_range]
  rfl

/-- The affine parameter of the actual `j`th directed segment. -/
def cycleSegmentParameter (c : R.BoundaryCycle N)
    (j : Fin (R.cycleDarts N c).card) (s : unitInterval) : unitInterval :=
  ⟨((j.val:ℝ)+(s:ℝ))/((R.cycleDarts N c).card:ℝ),by
    have hm : (0:ℝ)<(R.cycleDarts N c).card := by
      exact_mod_cast cycleDarts_card_pos N R c
    constructor
    · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) s.property.1) hm.le
    · apply (div_le_one hm).mpr
      have hj : (j.val:ℝ)+1≤(R.cycleDarts N c).card := by exact_mod_cast j.isLt
      linarith [s.property.2]⟩

lemma cycleCircleMap_segment (C : WP.External.FiniteCyclicIntervalGeometry.Classics)
    (c : R.BoundaryCycle N) (j : Fin (R.cycleDarts N c).card) (s : unitInterval) :
    cycleCircleMap N R C c (Quot.mk _ (cycleSegmentParameter N R c j s))=
      Quot.mk _ ((cycleDartEquiv N R c j).val,s) := by
  let m:=(R.cycleDarts N c).card
  let hm:=cycleDarts_card_pos N R c
  let h:=Classical.choose (C.circle m hm)
  have hs:=Classical.choose_spec (C.circle m hm) j s
  change cyclePolygonMap N R c
    (h (loopCircleHomeomorphAddCircle (Quot.mk _ (cycleSegmentParameter N R c j s))))=_
  rw [loopCircleHomeomorphAddCircle_mk]
  change cyclePolygonMap N R c (h ((((j.val:ℝ)+(s:ℝ))/(m:ℝ)):ℝ))=_
  rw [hs]
  rfl

/-- Actual closed walk with the canonical subdivision parameter. -/
def cycleClosedLoop (C : WP.External.FiniteCyclicIntervalGeometry.Classics)
    (c : R.BoundaryCycle N) : ClosedLoop (BoundaryWalkSpace N R) where
  map:=⟨fun t=>cycleCircleMap N R C c (Quot.mk _ t),
    (cycleCircleMap N R C c).continuous.comp continuous_quot_mk⟩
  closed:=congrArg (cycleCircleMap N R C c) (Quot.sound ⟨rfl,rfl⟩)

lemma cycleClosedLoop_simple (C : WP.External.FiniteCyclicIntervalGeometry.Classics)
    (c : R.BoundaryCycle N) : (cycleClosedLoop N R C c).Simple := by
  intro s hs t ht hst
  apply loopCircle_mk_injOn hs ht
  exact cycleCircleMap_injective N R C c hst

@[simp] lemma cycleClosedLoop_circleMap
    (C : WP.External.FiniteCyclicIntervalGeometry.Classics) (c : R.BoundaryCycle N) :
    (cycleClosedLoop N R C c).circleMap=cycleCircleMap N R C c := by
  ext z
  induction z using Quot.ind with
  | _ t=>rfl

lemma cycleClosedLoop_segment
    (C : WP.External.FiniteCyclicIntervalGeometry.Classics)
    (c : R.BoundaryCycle N) (j : Fin (R.cycleDarts N c).card) (s : unitInterval) :
    (cycleClosedLoop N R C c).map (cycleSegmentParameter N R c j s)=
      Quot.mk _ ((cycleDartEquiv N R c j).val,s) :=
  cycleCircleMap_segment N R C c j s

lemma cycleClosedLoop_trace (C : WP.External.FiniteCyclicIntervalGeometry.Classics)
    (c : R.BoundaryCycle N) :
    (cycleClosedLoop N R C c).trace={z | boundaryWalkCycle N R z=c} := by
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact boundaryWalkCycle_cycleCircleMap N R C c (Quot.mk _ t)
  · intro hz
    obtain ⟨w,hw⟩ := (cycleCircleMap_range N R C c).symm ▸ hz
    obtain ⟨t,ht⟩ :=Quot.exists_rep w
    refine ⟨t,?_⟩
    change cycleCircleMap N R C c (Quot.mk _ t)=z
    rw [ht]
    exact hw

lemma cycleClosedLoop_traces_disjoint (C : WP.External.FiniteCyclicIntervalGeometry.Classics)
    {c d : R.BoundaryCycle N} (hcd : c≠d) :
    Disjoint (cycleClosedLoop N R C c).trace (cycleClosedLoop N R C d).trace := by
  rw [cycleClosedLoop_trace,cycleClosedLoop_trace,Set.disjoint_left]
  intro z hc hd
  exact hcd (hc.symm.trans hd)

lemma cycleClosedLoop_traces_cover (C : WP.External.FiniteCyclicIntervalGeometry.Classics) :
    (⋃c,(cycleClosedLoop N R C c).trace)=Set.univ := by
  simp only [cycleClosedLoop_trace]
  apply Set.eq_univ_of_forall
  intro z
  exact Set.mem_iUnion.mpr ⟨boundaryWalkCycle N R z,rfl⟩

end WP.Critical.ShortConfiguration
