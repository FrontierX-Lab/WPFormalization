import WPFormalization.Critical.ShortConfigurationRecordingFinite
import WPFormalization.Critical.ShortConfigurationRecordingComponents
import WPFormalization.Critical.ShortConfigurationRecordingArcs
import WPFormalization.External.ShortFillingGeometry

/- Local G.3 cut-fiber counting backend. The cut and its intrinsic pieces are
actual realizations. A chosen lift supplies the direction of injection used
for counting; intrinsic primitive projections need not be injective. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset
open WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.Critical.PrimitivePacking
open scoped Classical

lemma curveParam_range_eq_trace (B : BorderedGeometry) (γ : B.curves.Primitive) :
    range (curveParam B γ)=B.curves.trace γ := by
  ext p
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨(B.curves.representative γ).axis t,⟨t,rfl⟩,rfl⟩
  · rintro ⟨q,⟨t,rfl⟩,rfl⟩
    exact ⟨t,rfl⟩

lemma primitive_trace_nonempty (B : BorderedGeometry) (γ : B.curves.Primitive) :
    (B.curves.trace γ).Nonempty := by
  rw [←curveParam_range_eq_trace B γ]
  exact range_nonempty _

lemma primitive_trace_preconnected (B : BorderedGeometry) (γ : B.curves.Primitive) :
    IsPreconnected (B.curves.trace γ) := by
  rw [←curveParam_range_eq_trace B γ]
  exact isPreconnected_range (curveParam_lipschitz B γ).continuous

variable {P : WP.PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}
  {A : AmbientRealization H} {T : MulticurveTopology.{u,v,w,z} G H}
  {g n k : ℕ} {o : T.Orbit g n k} {X : G.Moduli g n (fun _=>0)}
  {κ : Fin k→H.Primitive g n X} {hκ : T.orbitMem o X κ}

lemma trace_subset_cutComplement_of_disjoint (γ : H.Primitive g n X)
    (havoid : ∀e,Disjoint
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X γ))
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X (κ e)))) :
    (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆cutComplement A κ := by
  intro p hp e hpe
  exact (Set.disjoint_left.mp (havoid e)) hp hpe

lemma actual_primitive_ne_cut_of_disjoint (γ : H.Primitive g n X)
    (havoid : ∀e,Disjoint
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X γ))
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X (κ e)))) :
    ∀e,γ≠κ e := by
  intro e he
  obtain ⟨p,hp⟩:=primitive_trace_nonempty (A.model g n X) (A.primitiveEquiv g n X γ)
  exact (Set.disjoint_left.mp (havoid e)) hp (by simpa only [he] using hp)

/-- Nonempty connected actual primitive trace disjoint from every cut curve
lies in one uniquely determined intrinsic cut component. -/
lemma actual_cut_primitive_unique_piece
    (R : CutComponentRealization A T o X κ hκ) (γ : H.Primitive g n X)
    (havoid : ∀e,Disjoint
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X γ))
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X (κ e)))) :
    ∃!c : Fin (T.cut o).components,
      (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
        (R.piece c).point '' intrinsicInterior (R.piece c).model :=
  cut_realization_unique_piece R _
    (primitive_trace_nonempty _ _) (primitive_trace_preconnected _ _)
    (trace_subset_cutComplement_of_disjoint γ havoid)

/-- An actual ambient short primitive avoiding the cuts has a genuine short
intrinsic lift. The projection equality and length preservation are retained. -/
lemma actual_cut_primitive_short_lift
    (R : CutComponentRealization A T o X κ hκ) (γ : H.Primitive g n X)
    (L : ℝ) (hshort : H.length γ≤L)
    (havoid : ∀e,Disjoint
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X γ))
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X (κ e)))) :
    ∃c : Fin (T.cut o).components,∃β : (R.piece c).model.curves.Primitive,
      β∈(R.piece c).model.curves.short L ∧
      (R.piece c).primitiveProjection β=A.primitiveEquiv g n X γ ∧
      (R.piece c).model.curves.length β=H.length γ := by
  obtain ⟨c,hc,_⟩:=actual_cut_primitive_unique_piece R γ havoid
  obtain ⟨β,hβ⟩:=(R.piece c).lift_interior (A.primitiveEquiv g n X γ) hc
  have hlength : (R.piece c).model.curves.length β=H.length γ := by
    calc
      _=(A.model g n X).curves.length ((R.piece c).primitiveProjection β) :=
        ((R.piece c).length_preserved β).symm
      _=(A.model g n X).curves.length (A.primitiveEquiv g n X γ) := congrArg _ hβ
      _=H.length γ := A.length_eq g n X γ
  refine ⟨c,β,?_,hβ,hlength⟩
  apply ((R.piece c).model.curves.mem_short L β).mpr
  change (R.piece c).model.curves.length β≤L
  exact hlength ▸ hshort

/-- Actual finite tuple fibers: every coordinate is either one of the cut
edges or has trace avoiding all cut edges. No projection injectivity premise. -/
lemma actual_cut_piece_or_edge_tuple_card_bound
    (R : CutComponentRealization A T o X κ hκ) {r : ℕ}
    (K L : ℝ) (hK : ∀c,((R.piece c).model.negativeEuler:ℝ)≤K)
    (s : Finset (Fin r→H.Primitive g n X))
    (hshort : ∀t∈s,∀i,H.length (t i)≤L)
    (havoid : ∀t∈s,∀i,(∃e,κ e=t i) ∨ ∀e,Disjoint
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X (t i)))
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X (κ e)))) :
    s.card≤(k+(T.cut o).components*primitiveCountBound (4*Real.pi*K) L)^r := by
  apply intrinsic_piece_or_edge_tuple_card_bound
    (fun c=>(R.piece c).model) (fun c=>(R.piece c).double)
    (fun c β=>(A.primitiveEquiv g n X).symm ((R.piece c).primitiveProjection β))
    κ K L hK s
  intro t ht i
  rcases havoid t ht i with hedge|havoid'
  · exact Or.inl hedge
  · obtain ⟨c,β,hβ,hproject,_⟩:=actual_cut_primitive_short_lift R (t i) L (hshort t ht i) havoid'
    refine Or.inr ⟨c,β,hβ,?_⟩
    rw [hproject,Equiv.symm_apply_apply]

/-- The same estimate for a literal fiber of an actual tuple recording map.
The front end must prove edge-or-avoidance from its independently built record. -/
lemma actual_cut_recording_fiber_card_bound
    (R : CutComponentRealization A T o X κ hκ) {r : ℕ} {ρ : Type*}
    (record : (Fin r→H.Primitive g n X)→ρ) (a : ρ)
    (K L : ℝ) (hK : ∀c,((R.piece c).model.negativeEuler:ℝ)≤K)
    (s : Finset (Fin r→H.Primitive g n X))
    (hshort : ∀t∈s,∀i,H.length (t i)≤L)
    (havoid : ∀t∈s,record t=a→∀i,(∃e,κ e=t i) ∨ ∀e,Disjoint
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X (t i)))
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X (κ e)))) :
    (s.filter (fun t=>record t=a)).card≤
      (k+(T.cut o).components*primitiveCountBound (4*Real.pi*K) L)^r := by
  apply actual_cut_piece_or_edge_tuple_card_bound R K L hK
    (s.filter (fun t=>record t=a))
  · intro t ht i
    exact hshort t (Finset.mem_filter.mp ht).1 i
  · intro t ht i
    exact havoid t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2 i

end WP.Critical.ShortConfiguration
