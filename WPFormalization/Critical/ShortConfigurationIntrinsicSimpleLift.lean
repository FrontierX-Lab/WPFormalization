import WPFormalization.Critical.ShortConfigurationRecordingIntersections

noncomputable section
set_option maxHeartbeats 0
universe u v w
namespace WP.Critical.ShortConfiguration
open Set
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry

/-- Injectivity on one period identifies all equal values modulo that period. -/
lemma periodic_injOn_ico_eq_implies_zsmul {Y : Type*}
    (f : ℝ→Y) (ell : ℝ) (hell : 0<ell)
    (hperiod : Function.Periodic f ell) (hinj : Set.InjOn f (Ico 0 ell))
    {s t : ℝ} (heq : f s=f t) : ∃n:ℤ,t-s=n•ell := by
  have hnorm (a : ℝ) : f (toIcoMod hell 0 a)=f a :=
    hperiod.sub_zsmul_eq (toIcoDiv hell 0 a)
  have hmod : toIcoMod hell 0 s=toIcoMod hell 0 t := by
    apply hinj (toIcoMod_mem_Ico' hell s) (toIcoMod_mem_Ico' hell t)
    exact (hnorm s).trans (heq.trans (hnorm t).symm)
  exact (toIcoMod_eq_toIcoMod hell).mp hmod

/-- Rotation and orientation reversal preserve one-period injectivity. -/
lemma periodic_injOn_ico_phase {Y : Type*}
    (f : ℝ→Y) (ell : ℝ) (hell : 0<ell)
    (hperiod : Function.Periodic f ell) (hinj : Set.InjOn f (Ico 0 ell))
    (phase : ℝ) (reverse : Bool) :
    Set.InjOn (fun t=>f (if reverse then phase-t else phase+t)) (Ico 0 ell) := by
  intro s hs t ht heq
  have hdiff : ∃n:ℤ,t-s=n•ell := by
    cases reverse with
    | false =>
        obtain ⟨n,hn⟩:=periodic_injOn_ico_eq_implies_zsmul f ell hell hperiod hinj heq
        exact ⟨n,by simpa only [Bool.false_eq_true,ite_false,add_sub_add_left_eq_sub] using hn⟩
    | true =>
        obtain ⟨n,hn⟩:=periodic_injOn_ico_eq_implies_zsmul f ell hell hperiod hinj heq
        refine ⟨-n,?_⟩
        simp only [neg_zsmul]
        simp only [ite_true] at hn
        linarith
  have hmod : toIcoMod hell 0 s=toIcoMod hell 0 t :=
    (toIcoMod_eq_toIcoMod hell).mpr hdiff
  rw [(toIcoMod_eq_self hell).mpr (by simpa only [zero_add] using hs),
    (toIcoMod_eq_self hell).mpr (by simpa only [zero_add] using ht)] at hmod
  exact hmod

/-- Simplicity of an actual projected primitive forces intrinsic simplicity.
Only the actual phase/orientation axis equation and preserved period are used. -/
lemma intrinsicPiece_simple_of_projection_simple
    {B : BorderedGeometry.{u,v}} (I : IntrinsicPiece B)
    (β : I.model.curves.Primitive) (hsimple : SimpleTrace B (I.primitiveProjection β)) :
    SimpleTrace I.model β := by
  obtain ⟨phase,reverse,haxis⟩:=I.axis_map β
  have hpos : 0<B.curves.length (I.primitiveProjection β) :=
    (B.curves.representative (I.primitiveProjection β)).period_pos
  have hinj:=periodic_injOn_ico_phase (curveParam B (I.primitiveProjection β))
    (B.curves.length (I.primitiveProjection β)) hpos
    (curveParam_periodic B (I.primitiveProjection β)) hsimple phase reverse
  intro s hs t ht heq
  apply hinj
    (by simpa only [I.length_preserved β] using hs)
    (by simpa only [I.length_preserved β] using ht)
  exact (haxis s).symm.trans ((congrArg I.point heq).trans (haxis t))

lemma intrinsicPiece_simple_of_projection_eq
    {B : BorderedGeometry.{u,v}} (I : IntrinsicPiece B)
    (β : I.model.curves.Primitive) (γ : B.curves.Primitive)
    (hproject : I.primitiveProjection β=γ) (hsimple : SimpleTrace B γ) :
    SimpleTrace I.model β := by
  apply intrinsicPiece_simple_of_projection_simple I β
  simpa only [hproject] using hsimple

/-- A genuine interior lift of a simple actual ambient primitive is simple,
with literal projection and length equalities retained. The actual piece and
trace containment are supplied separately, rather than constructed here. -/
lemma intrinsicPiece_exists_simple_lift
    {B : BorderedGeometry.{u,v}} (I : IntrinsicPiece B) (γ : B.curves.Primitive)
    (htrace : B.curves.trace γ⊆I.point '' intrinsicInterior I.model)
    (hsimple : SimpleTrace B γ) :
    ∃β : I.model.curves.Primitive,I.primitiveProjection β=γ ∧
      SimpleTrace I.model β ∧ I.model.curves.length β=B.curves.length γ := by
  obtain ⟨β,hproject⟩:=I.lift_interior γ htrace
  refine ⟨β,hproject,intrinsicPiece_simple_of_projection_eq I β γ hproject hsimple,?_⟩
  calc
    _=B.curves.length (I.primitiveProjection β) :=(I.length_preserved β).symm
    _=B.curves.length γ :=congrArg B.curves.length hproject

end WP.Critical.ShortConfiguration
