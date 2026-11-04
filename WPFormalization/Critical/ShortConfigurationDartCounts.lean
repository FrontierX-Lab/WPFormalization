import WPFormalization.Critical.ShortConfigurationRecordingEmbedded
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Topology.Homotopy.Basic
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.ShortConfiguration
open Set Finset
open scoped Classical
variable {X : Type u} [MetricSpace X] (N : EmbeddedNetwork.{u,v} X)

/-- Both ends of every actual edge, including both ends of a loop. -/
def NetworkDart := N.Edge × Bool
instance : Fintype (NetworkDart N) := inferInstanceAs (Fintype (N.Edge × Bool))
instance : TopologicalSpace (NetworkDart N) := ⊥
instance : DiscreteTopology (NetworkDart N) := ⟨rfl⟩

def dartStart (d : NetworkDart N) : X := N.curve d.1 (if d.2 then N.finish d.1 else N.start d.1)
def dartFinish (d : NetworkDart N) : X := N.curve d.1 (if d.2 then N.start d.1 else N.finish d.1)
def reverseDart : Equiv.Perm (NetworkDart N) where
  toFun d := (d.1,!d.2)
  invFun d := (d.1,!d.2)
  left_inv d := by rcases d with ⟨e,b⟩;cases b <;> rfl
  right_inv d := by rcases d with ⟨e,b⟩;cases b <;> rfl

lemma reverseDart_start (d : NetworkDart N) : dartStart N (reverseDart N d)=dartFinish N d := by
  rcases d with ⟨e,b⟩;cases b <;> rfl

/-- A rotation is not supplied by the local graph constructor. A geometric
regular neighborhood must identify its boundary with this rotation's walks. -/
structure NetworkRotation where
  successor : Equiv.Perm (NetworkDart N)
  start_eq : ∀d,dartStart N (successor d)=dartStart N d
  vertex_cycles : ∀d e,successor.SameCycle d e ↔ dartStart N d=dartStart N e

def NetworkRotation.face (R : NetworkRotation N) : Equiv.Perm (NetworkDart N) :=
  R.successor * reverseDart N

lemma NetworkRotation.face_adjacent (R : NetworkRotation N) (d : NetworkDart N) :
    dartStart N (R.face N d)=dartFinish N d := by
  exact (R.start_eq (reverseDart N d)).trans (reverseDart_start N d)

def dartParameter (d : NetworkDart N) (t : unitInterval) : ℝ :=
  if d.2 then (1-(t:ℝ))*N.finish d.1+(t:ℝ)*N.start d.1
  else (1-(t:ℝ))*N.start d.1+(t:ℝ)*N.finish d.1

def dartPoint (p : NetworkDart N × unitInterval) : X := N.curve p.1.1 (dartParameter N p.1 p.2)

lemma dartPoint_zero (d : NetworkDart N) : dartPoint N (d,0)=dartStart N d := by
  rcases d with ⟨e,b⟩;cases b <;> simp [dartPoint,dartParameter,dartStart]
lemma dartPoint_one (d : NetworkDart N) : dartPoint N (d,1)=dartFinish N d := by
  rcases d with ⟨e,b⟩;cases b <;> simp [dartPoint,dartParameter,dartFinish]

lemma dartPoint_continuous : Continuous (dartPoint N) := by
  apply continuous_prod_of_discrete_left.mpr
  intro d
  apply (N.lipschitz d.1).continuous.comp
  rcases d with ⟨e,b⟩
  cases b <;> dsimp [dartParameter] <;> fun_prop

lemma dartPoint_mem_support (p : NetworkDart N × unitInterval) : dartPoint N p∈N.support := by
  have ht0 := p.2.property.1
  have ht1 := p.2.property.2
  have he := le_of_lt (N.interval_pos p.1.1)
  have ha := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr he)
  have hb := mul_nonneg ht0 (sub_nonneg.mpr he)
  refine mem_iUnion.mpr ⟨p.1.1,dartParameter N p.1 p.2,?_,rfl⟩
  unfold dartParameter
  split_ifs <;> constructor <;> nlinarith only [ha,hb]

/-- Exact endpoint identifications in the boundary walks. Each dart contributes
one interval; the next interval is rho(reverse(d)). -/
def boundaryWalkRelation (R : NetworkRotation N) (p q : NetworkDart N × unitInterval) : Prop :=
  p.2=1 ∧ q=(R.face N p.1,0)
def BoundaryWalkSpace (R : NetworkRotation N) := Quot (boundaryWalkRelation N R)
instance (R : NetworkRotation N) : TopologicalSpace (BoundaryWalkSpace N R) :=
  inferInstanceAs (TopologicalSpace (Quot (boundaryWalkRelation N R)))

lemma boundaryWalk_respects (R : NetworkRotation N) :
    ∀p q,boundaryWalkRelation N R p q→dartPoint N p=dartPoint N q := by
  intro ⟨d,t⟩ q h
  rcases h with ⟨ht,hq⟩
  dsimp at ht hq
  subst q
  subst t
  exact (dartPoint_one N d).trans ((R.face_adjacent N d).symm.trans (dartPoint_zero N (R.face N d)).symm)

def boundaryWalk (R : NetworkRotation N) : C(BoundaryWalkSpace N R,X) where
  toFun := Quot.lift (dartPoint N) (boundaryWalk_respects N R)
  continuous_toFun := continuous_quot_lift (boundaryWalk_respects N R) (dartPoint_continuous N)

lemma boundaryWalk_mem_support (R : NetworkRotation N) (p : BoundaryWalkSpace N R) :
    boundaryWalk N R p∈N.support := by
  induction p using Quot.ind with | _ p => exact dartPoint_mem_support N p


lemma EmbeddedNetwork.support_compact : IsCompact N.support := by
  exact isCompact_iUnion (fun e => isCompact_Icc.image (N.lipschitz e).continuous)

def NetworkRotation.BoundaryCycle (R : NetworkRotation N) :=
  Quotient (Equiv.Perm.SameCycle.setoid (R.face N))
instance (R : NetworkRotation N) : Finite (R.BoundaryCycle N) :=
  inferInstanceAs (Finite (Quotient (Equiv.Perm.SameCycle.setoid (R.face N))))
instance (R : NetworkRotation N) : Fintype (R.BoundaryCycle N) := Fintype.ofFinite _

def NetworkRotation.dartCycle (R : NetworkRotation N) (d : NetworkDart N) : R.BoundaryCycle N :=
  @Quotient.mk' _ (Equiv.Perm.SameCycle.setoid (R.face N)) d

def NetworkRotation.cycleDarts (R : NetworkRotation N) (c : R.BoundaryCycle N) : Finset (NetworkDart N) :=
  Finset.univ.filter (fun d => R.dartCycle N d=c)

@[simp] lemma NetworkRotation.mem_cycleDarts (R : NetworkRotation N)
    (c : R.BoundaryCycle N) (d : NetworkDart N) :
    d ∈ R.cycleDarts N c ↔ R.dartCycle N d = c := by
  simp [NetworkRotation.cycleDarts]

lemma NetworkRotation.existsUnique_cycleDarts (R : NetworkRotation N) (d : NetworkDart N) :
    ∃! c : R.BoundaryCycle N, d ∈ R.cycleDarts N c := by
  refine ⟨R.dartCycle N d, (R.mem_cycleDarts N _ _).mpr rfl, ?_⟩
  intro c hc
  exact ((R.mem_cycleDarts N c d).mp hc).symm

lemma NetworkRotation.cycleDarts_disjoint (R : NetworkRotation N)
    {c e : R.BoundaryCycle N} (h : c ≠ e) :
    Disjoint (R.cycleDarts N c) (R.cycleDarts N e) := by
  apply Finset.disjoint_left.mpr
  intro d hc he
  exact h (((R.mem_cycleDarts N c d).mp hc).symm.trans
    ((R.mem_cycleDarts N e d).mp he))

lemma NetworkRotation.boundaryCycle_card_le (R : NetworkRotation N) :
    Nat.card (R.BoundaryCycle N)≤2*Nat.card N.Edge := by
  have hsurj : Function.Surjective (R.dartCycle N) := by
    intro c
    induction c using Quotient.ind with | _ d => exact ⟨d,rfl⟩
  calc
    Nat.card (R.BoundaryCycle N)≤Nat.card (NetworkDart N) :=
      Nat.card_le_card_of_surjective (R.dartCycle N) hsurj
    _ = 2*Nat.card N.Edge := by simp [NetworkDart,Nat.mul_comm]

lemma NetworkRotation.sum_cycleDarts {M : Type*} [AddCommMonoid M]
    (R : NetworkRotation N) (w : NetworkDart N→M) :
    ∑c,∑d∈R.cycleDarts N c,w d =∑d,w d :=
  Finset.sum_fiberwise Finset.univ (R.dartCycle N) w

lemma NetworkRotation.sum_boundary_weights (R : NetworkRotation N) (w : N.Edge→ℝ) :
    ∑c,∑d∈R.cycleDarts N c,w d.1=2*∑e,w e := by
  rw [R.sum_cycleDarts N]
  change (∑d:N.Edge×Bool,w d.1)=_
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

lemma subdivision_total_length (ell : ℝ) (s : Finset ℝ) (hzero : 0∈s)
    (hnonneg : ∀t∈s,0≤t) :
    ∑j:Fin s.card,(subdivisionEnd ell s j-subdivisionStart s j)=ell := by
  let f : ℕ→ℝ := fun k => if hk:k<s.card then s.orderEmbOfFin rfl ⟨k,hk⟩ else ell
  have hc : 0<s.card := Finset.card_pos.mpr ⟨0,hzero⟩
  let : NeZero s.card := ⟨Nat.ne_zero_of_lt hc⟩
  have hf0 : f 0=0 := by
    rw [show f 0=s.orderEmbOfFin rfl ⟨0,hc⟩ by simp [f,hc]]
    apply le_antisymm
    · let j := (s.orderIsoOfFin rfl).symm ⟨0,hzero⟩
      have hj : s.orderEmbOfFin rfl j=0 := congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨0,hzero⟩)
      exact ((s.orderEmbOfFin rfl).monotone (Fin.zero_le j)).trans (le_of_eq hj)
    · exact hnonneg _ (s.orderEmbOfFin_mem rfl _)
  have hfm : f s.card=ell := by simp [f]
  calc
    _ =∑j:Fin s.card,(f (j.val+1)-f j.val) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hs : f j.val=subdivisionStart s j := by simp [f,j.isLt,subdivisionStart]
      have he : f (j.val+1)=subdivisionEnd ell s j := by
        unfold f subdivisionEnd
        split_ifs <;> rfl
      rw [hs,he]
    _ =∑j∈Finset.range s.card,(f (j+1)-f j) := Fin.sum_univ_eq_sum_range (fun j => f (j+1)-f j) s.card
    _ = f s.card-f 0 := Finset.sum_range_sub f s.card
    _ =ell := by rw [hf0,hfm,sub_zero]


variable (B : WP.External.HyperbolicPacking.BorderedGeometry)
  (H : WP.External.ShortFillingGeometry.SegmentClassics B) {r : ℕ}
  (γ : Fin r→B.curves.Primitive) (hinj : Function.Injective γ)
  (hsimple : ∀i,WP.External.ShortFillingGeometry.SimpleTrace B (γ i))
  (L : ℝ) (hL : 0<L) (hlength : ∀i,B.curves.length (γ i)≤L)

local notation "NN" => tupleEmbeddedNetwork B H γ hinj hsimple L hL hlength

lemma tupleEmbeddedNetwork_total_length :
    ∑e:(NN).Edge,((NN).finish e-(NN).start e)=∑i,B.curves.length (γ i) := by
  change (∑e:Σi:Fin r,Fin (breakpoints B H γ hinj hsimple L hL hlength i).card,
    (arcEnd B H γ hinj hsimple L hL hlength e-arcStart B H γ hinj hsimple L hL hlength e))=_
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  exact subdivision_total_length (B.curves.length (γ i))
    (breakpoints B H γ hinj hsimple L hL hlength i)
    (zero_mem_breakpoints B H γ hinj hsimple L hL hlength i)
    (fun t ht => (breakpoints_mem_period B H γ hinj hsimple L hL hlength i ht).1)

lemma tupleEmbeddedNetwork_boundary_walk_length (R : NetworkRotation NN) :
    ∑c,∑d∈R.cycleDarts NN c,((NN).finish d.1-(NN).start d.1)=2*∑i,B.curves.length (γ i) := by
  exact (R.sum_boundary_weights NN (fun e : (NN).Edge => (NN).finish e - (NN).start e)).trans
    (congrArg (fun z : ℝ => 2*z)
      (tupleEmbeddedNetwork_total_length B H γ hinj hsimple L hL hlength))

lemma tupleEmbeddedNetwork_boundary_walk_length_le (R : NetworkRotation NN) :
    ∑c,∑d∈R.cycleDarts NN c,((NN).finish d.1-(NN).start d.1)≤2*r*L := by
  rw [tupleEmbeddedNetwork_boundary_walk_length B H γ hinj hsimple L hL hlength R]
  calc
    2*∑i,B.curves.length (γ i)≤2*∑_i:Fin r,L := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi=>hlength i)) (by norm_num)
    _=2*r*L := by simp [mul_assoc]

lemma tupleEmbeddedNetwork_boundary_cycle_bound (R : NetworkRotation NN) :
    Nat.card (R.BoundaryCycle NN)≤2*(r*(r*r*(Nat.floor (L/WP.External.ShortFillingGeometry.segmentScale L)+1)^2+1)) := by
  exact (R.boundaryCycle_card_le NN).trans (Nat.mul_le_mul_left 2
    (tupleEmbeddedNetwork_edges_bound B H γ hinj hsimple L hL hlength))

end WP.Critical.ShortConfiguration
