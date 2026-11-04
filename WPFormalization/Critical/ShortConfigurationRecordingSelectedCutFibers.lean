import WPFormalization.Critical.ShortConfigurationRecordingCutFibers

noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset
open WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.Critical.PrimitivePacking
open scoped Classical

/-- A pool of actual intrinsic short primitives from the selected pieces only. -/
def selectedIntrinsicPrimitivePool {ι : Type*} (B : ι→BorderedGeometry.{u,v})
    (selected : Finset ι) (L : ℝ) : Finset (Σc:ι,(B c).curves.Primitive) :=
  selected.sigma (fun c=>(B c).curves.short L)

lemma selectedIntrinsicPrimitivePool_card_le {ι : Type*}
    (B : ι→BorderedGeometry.{u,v}) (D : ∀c,DoublingClassics (B c))
    (selected : Finset ι) (K L : ℝ)
    (hK : ∀c∈selected,((B c).negativeEuler:ℝ)≤K) :
    (selectedIntrinsicPrimitivePool B selected L).card≤
      selected.card*primitiveCountBound (4*Real.pi*K) L := by
  rw [selectedIntrinsicPrimitivePool,Finset.card_sigma]
  calc
    _ ≤ ∑_c∈selected,primitiveCountBound (4*Real.pi*K) L := by
      apply sum_le_sum
      intro c hc
      exact intrinsic_short_card_le K L (B c) (D c) (hK c hc)
    _ = _ := by simp

/-- Selected pieces may have bounded topology even when the ambient complement
has additional pieces of arbitrarily large genus. No bound is imposed on them. -/
lemma intrinsic_selected_piece_or_edge_tuple_card_bound
    {α : Type w} {ι : Type*} {r k : ℕ}
    (B : ι→BorderedGeometry.{u,v}) (D : ∀c,DoublingClassics (B c))
    (project : ∀c,(B c).curves.Primitive→α) (edges : Fin k→α)
    (selected : Finset ι) (K L : ℝ)
    (hK : ∀c∈selected,((B c).negativeEuler:ℝ)≤K)
    (s : Finset (Fin r→α))
    (hlift : ∀t∈s,∀i,(∃e,edges e=t i) ∨
      ∃c∈selected,∃β,β∈(B c).curves.short L ∧ project c β=t i) :
    s.card≤(k+selected.card*primitiveCountBound (4*Real.pi*K) L)^r := by
  let pieces:=selectedIntrinsicPrimitivePool B selected L
  let pool : Finset (Fin k ⊕ (Σc:ι,(B c).curves.Primitive)) :=
    (univ : Finset (Fin k)).disjSum pieces
  let projectPool : (Fin k ⊕ (Σc:ι,(B c).curves.Primitive))→α :=
    Sum.elim edges (fun b=>project b.1 b.2)
  have hc : pool.card≤k+selected.card*primitiveCountBound (4*Real.pi*K) L := by
    simp only [pool,card_disjSum,card_univ,Fintype.card_fin]
    exact Nat.add_le_add_left (selectedIntrinsicPrimitivePool_card_le B D selected K L hK) k
  refine (tuple_card_le_pool_pow s pool projectPool ?_).trans (Nat.pow_le_pow_left hc r)
  intro t ht i
  rcases hlift t ht i with ⟨e,he⟩|⟨c,hc,β,hβ,he⟩
  · exact ⟨Sum.inl e,by simp [pool],he⟩
  · exact ⟨Sum.inr ⟨c,β⟩,by simp [pool,pieces,selectedIntrinsicPrimitivePool,hc,hβ],he⟩

variable {P : WP.PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}
  {A : AmbientRealization H} {T : MulticurveTopology.{u,v,w,z} G H}
  {g n k : ℕ} {o : T.Orbit g n k} {X : G.Moduli g n (fun _=>0)}
  {κ : Fin k→H.Primitive g n X} {hκ : T.orbitMem o X κ}

lemma actual_cut_trace_subset_complement_of_piece
    (R : CutComponentRealization A T o X κ hκ) (γ : H.Primitive g n X)
    (c : Fin (T.cut o).components)
    (htrace : (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
      (R.piece c).point '' intrinsicInterior (R.piece c).model) :
    (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆cutComplement A κ := by
  intro p hp
  obtain ⟨hpu,_⟩:=R.image_eq c ▸ htrace hp
  exact hpu

lemma actual_cut_primitive_avoid_of_piece
    (R : CutComponentRealization A T o X κ hκ) (γ : H.Primitive g n X)
    (c : Fin (T.cut o).components)
    (htrace : (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
      (R.piece c).point '' intrinsicInterior (R.piece c).model) :
    ∀e,Disjoint
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X γ))
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X (κ e))) := by
  intro e
  apply Set.disjoint_left.mpr
  intro p hp hpe
  exact actual_cut_trace_subset_complement_of_piece R γ c htrace hp e hpe

/-- The original unique-piece theorem identifies the selected piece; the
frontend must establish the displayed actual trace containment. -/
lemma actual_cut_primitive_unique_selected_piece
    (R : CutComponentRealization A T o X κ hκ)
    (selected : Finset (Fin (T.cut o).components)) (γ : H.Primitive g n X)
    (hselected : ∃c∈selected,
      (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
        (R.piece c).point '' intrinsicInterior (R.piece c).model) :
    ∃!c : {c // c∈selected},
      (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
        (R.piece c.val).point '' intrinsicInterior (R.piece c.val).model := by
  obtain ⟨c,hc,htrace⟩:=hselected
  obtain ⟨d,_,hd⟩:=actual_cut_primitive_unique_piece R γ
    (actual_cut_primitive_avoid_of_piece R γ c htrace)
  refine ⟨⟨c,hc⟩,htrace,?_⟩
  intro e he
  apply Subtype.ext
  exact (hd e.val he).trans (hd c htrace).symm

/-- Lift into the supplied actual component, retaining literal projection and
length preservation; no projection injectivity is assumed. -/
lemma actual_cut_primitive_short_lift_in_piece
    (R : CutComponentRealization A T o X κ hκ) (γ : H.Primitive g n X)
    (c : Fin (T.cut o).components) (L : ℝ) (hshort : H.length γ≤L)
    (htrace : (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
      (R.piece c).point '' intrinsicInterior (R.piece c).model) :
    ∃β : (R.piece c).model.curves.Primitive,
      β∈(R.piece c).model.curves.short L ∧
      (R.piece c).primitiveProjection β=A.primitiveEquiv g n X γ ∧
      (R.piece c).model.curves.length β=H.length γ := by
  obtain ⟨β,hβ⟩:=(R.piece c).lift_interior (A.primitiveEquiv g n X γ) htrace
  have hlength : (R.piece c).model.curves.length β=H.length γ := by
    calc
      _=(A.model g n X).curves.length ((R.piece c).primitiveProjection β) :=
        ((R.piece c).length_preserved β).symm
      _=(A.model g n X).curves.length (A.primitiveEquiv g n X γ) := congrArg _ hβ
      _=H.length γ := A.length_eq g n X γ
  refine ⟨β,?_,hβ,hlength⟩
  apply ((R.piece c).model.curves.mem_short L β).mpr
  change (R.piece c).model.curves.length β≤L
  exact hlength ▸ hshort

lemma actual_cut_primitive_short_lift_in_selected
    (R : CutComponentRealization A T o X κ hκ)
    (selected : Finset (Fin (T.cut o).components)) (γ : H.Primitive g n X)
    (L : ℝ) (hshort : H.length γ≤L)
    (hselected : ∃c∈selected,
      (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
        (R.piece c).point '' intrinsicInterior (R.piece c).model) :
    ∃c∈selected,∃β : (R.piece c).model.curves.Primitive,
      β∈(R.piece c).model.curves.short L ∧
      (R.piece c).primitiveProjection β=A.primitiveEquiv g n X γ ∧
      (R.piece c).model.curves.length β=H.length γ := by
  obtain ⟨c,hc,_⟩:=actual_cut_primitive_unique_selected_piece R selected γ hselected
  obtain ⟨β,hβ,hproject,hlength⟩:=actual_cut_primitive_short_lift_in_piece R γ c.val L hshort hc
  exact ⟨c.val,c.property,β,hβ,hproject,hlength⟩

/-- Actual tuple fibers use a pool over selected components only. Selected
membership and its Euler budget remain ordinary frontend proof obligations. -/
lemma actual_cut_selected_piece_or_edge_tuple_card_bound
    (R : CutComponentRealization A T o X κ hκ) {r : ℕ}
    (selected : Finset (Fin (T.cut o).components))
    (K L : ℝ) (hK : ∀c∈selected,((R.piece c).model.negativeEuler:ℝ)≤K)
    (s : Finset (Fin r→H.Primitive g n X))
    (hshort : ∀t∈s,∀i,H.length (t i)≤L)
    (hselected : ∀t∈s,∀i,(∃e,κ e=t i) ∨ ∃c∈selected,
      (A.model g n X).curves.trace (A.primitiveEquiv g n X (t i))⊆
        (R.piece c).point '' intrinsicInterior (R.piece c).model) :
    s.card≤(k+selected.card*primitiveCountBound (4*Real.pi*K) L)^r := by
  apply intrinsic_selected_piece_or_edge_tuple_card_bound
    (fun c=>(R.piece c).model) (fun c=>(R.piece c).double)
    (fun c β=>(A.primitiveEquiv g n X).symm ((R.piece c).primitiveProjection β))
    κ selected K L hK s
  intro t ht i
  rcases hselected t ht i with hedge|hselected'
  · exact Or.inl hedge
  · obtain ⟨c,hc,β,hβ,hproject,_⟩:=actual_cut_primitive_short_lift_in_selected
      R selected (t i) L (hshort t ht i) hselected'
    refine Or.inr ⟨c,hc,β,hβ,?_⟩
    rw [hproject,Equiv.symm_apply_apply]

lemma actual_cut_selected_recording_fiber_card_bound
    (R : CutComponentRealization A T o X κ hκ) {r : ℕ} {ρ : Type*}
    (record : (Fin r→H.Primitive g n X)→ρ) (a : ρ)
    (selected : Finset (Fin (T.cut o).components))
    (K L : ℝ) (hK : ∀c∈selected,((R.piece c).model.negativeEuler:ℝ)≤K)
    (s : Finset (Fin r→H.Primitive g n X))
    (hshort : ∀t∈s,∀i,H.length (t i)≤L)
    (hselected : ∀t∈s,record t=a→∀i,(∃e,κ e=t i) ∨ ∃c∈selected,
      (A.model g n X).curves.trace (A.primitiveEquiv g n X (t i))⊆
        (R.piece c).point '' intrinsicInterior (R.piece c).model) :
    (s.filter (fun t=>record t=a)).card≤
      (k+selected.card*primitiveCountBound (4*Real.pi*K) L)^r := by
  apply actual_cut_selected_piece_or_edge_tuple_card_bound R selected K L hK
    (s.filter (fun t=>record t=a))
  · intro t ht i
    exact hshort t (Finset.mem_filter.mp ht).1 i
  · intro t ht i
    exact hselected t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2 i

end WP.Critical.ShortConfiguration
