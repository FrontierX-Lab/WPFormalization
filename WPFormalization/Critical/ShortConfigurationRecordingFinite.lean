import WPFormalization.Critical.PrimitiveCount
noncomputable section
set_option maxHeartbeats 0
universe u v w
namespace WP.Critical.ShortConfiguration
open Finset Set
open WP.External.HyperbolicPacking
open WP.Critical.PrimitivePacking
open scoped Classical

/- A finite algebraic choice lemma; using it for a geometric recording requires
constructing the intrinsic lifts. It assumes neither G.3 nor a fiber count. -/
lemma tuple_card_le_pool_pow {α β : Type*} {r : ℕ} (s : Finset (Fin r→α))
    (pool : Finset β) (project : β→α)
    (hcover : ∀t∈s,∀i,∃b∈pool,project b=t i) : s.card≤pool.card^r := by
  have hc : ∀t : {t //t∈s},∀i:Fin r,∃b:{b //b∈pool},project b.val=t.val i := by
    intro t i
    obtain ⟨b,hb,he⟩ := hcover t.val t.property i
    exact ⟨⟨b,hb⟩,he⟩
  choose lift hlift using hc
  have hi : Function.Injective lift := by
    intro t t' he
    apply Subtype.ext
    funext i
    calc
      t.val i=project ((lift t i).val) := (hlift t i).symm
      _=project ((lift t' i).val) := by rw [he]
      _=t'.val i := hlift t' i
  have hb := Fintype.card_le_of_injective lift hi
  simpa using hb

lemma intrinsic_short_card_le (K L : ℝ) (B : BorderedGeometry) (D : DoublingClassics B)
    (hK : (B.negativeEuler:ℝ)≤K) :
    (B.curves.short L).card≤primitiveCountBound (4*Real.pi*K) L :=
  (short_card_le_double B D L).trans
    (complete_short_card_bound D.curves D.packing _ L (double_area_bound B D K hK))

/- Primitive projection to the ambient surface need not be injective: formal
boundary circles may have the same ambient image. Choosing actual intrinsic
lifts of ambient curves produces the injection in the required direction. -/
lemma intrinsic_piece_tuple_card_bound {α : Type w} {Q r : ℕ}
    (B : Fin Q→BorderedGeometry.{u,v}) (D : ∀j,DoublingClassics (B j))
    (project : ∀j,(B j).curves.Primitive→α) (K L : ℝ)
    (hK : ∀j,((B j).negativeEuler:ℝ)≤K)
    (s : Finset (Fin r→α))
    (hlift : ∀t∈s,∀i,∃j β,β∈(B j).curves.short L ∧ project j β=t i) :
    s.card≤(Q*primitiveCountBound (4*Real.pi*K) L)^r := by
  let pool : Finset (Σj:Fin Q,(B j).curves.Primitive) :=
    univ.sigma (fun j=>(B j).curves.short L)
  have hc : pool.card≤Q*primitiveCountBound (4*Real.pi*K) L := by
    rw [Finset.card_sigma]
    calc
      _ ≤ ∑_j:Fin Q,primitiveCountBound (4*Real.pi*K) L := by
        apply sum_le_sum
        intro j hj
        exact intrinsic_short_card_le K L (B j) (D j) (hK j)
      _ = _ := by simp
  refine (tuple_card_le_pool_pow s pool (fun b=>project b.1 b.2) ?_).trans (Nat.pow_le_pow_left hc r)
  intro t ht i
  obtain ⟨j,β,hβ,he⟩ := hlift t ht i
  exact ⟨⟨j,β⟩,by simp [pool,hβ],he⟩

/- The pool also retains original tuple curves that become isolated cut
edges. Formal boundary copies are not identified as intrinsic classes. -/
lemma intrinsic_piece_or_edge_tuple_card_bound {α : Type w} {Q r k : ℕ}
    (B : Fin Q→BorderedGeometry.{u,v}) (D : ∀j,DoublingClassics (B j))
    (project : ∀j,(B j).curves.Primitive→α) (edges : Fin k→α) (K L : ℝ)
    (hK : ∀j,((B j).negativeEuler:ℝ)≤K)
    (s : Finset (Fin r→α))
    (hlift : ∀t∈s,∀i,(∃e,edges e=t i) ∨
      ∃j β,β∈(B j).curves.short L ∧ project j β=t i) :
    s.card≤(k+Q*primitiveCountBound (4*Real.pi*K) L)^r := by
  let pieces : Finset (Σj:Fin Q,(B j).curves.Primitive) :=
    univ.sigma (fun j=>(B j).curves.short L)
  let pool : Finset (Fin k ⊕ (Σj:Fin Q,(B j).curves.Primitive)) :=
    (univ : Finset (Fin k)).disjSum pieces
  let π : (Fin k ⊕ (Σj:Fin Q,(B j).curves.Primitive))→α :=
    Sum.elim edges (fun b=>project b.1 b.2)
  have hc : pool.card≤k+Q*primitiveCountBound (4*Real.pi*K) L := by
    simp only [pool,card_disjSum,card_univ,Fintype.card_fin]
    apply Nat.add_le_add_left
    rw [Finset.card_sigma]
    calc
      _ ≤ ∑_j:Fin Q,primitiveCountBound (4*Real.pi*K) L :=
        sum_le_sum (fun j _ => intrinsic_short_card_le K L (B j) (D j) (hK j))
      _ = _ := by simp
  refine (tuple_card_le_pool_pow s pool π ?_).trans (Nat.pow_le_pow_left hc r)
  intro t ht i
  rcases hlift t ht i with ⟨e,he⟩|⟨j,β,hβ,he⟩
  · exact ⟨Sum.inl e,by simp [pool],he⟩
  · exact ⟨Sum.inr ⟨j,β⟩,by simp [pool,pieces,hβ],he⟩

/- Finite recording arithmetic. The recording map and the actual intrinsic
lifts must be constructed independently; no asymptotic result is assumed. -/
lemma count_le_recording_sum {α ρ : Type*} (s : Finset α) (records : Finset ρ)
    (record : α→ρ) (hrecord : ∀a∈s,record a∈records)
    (bound : ρ→ℕ) (hfiber : ∀R∈records,(s.filter (fun a=>record a=R)).card≤bound R) :
    s.card≤∑R∈records,bound R := by
  have he : ∑R∈records,(s.filter (fun a=>record a=R)).card=s.card := by
    simpa using (Finset.sum_fiberwise_of_maps_to' hrecord (fun _=> (1:ℕ)))
  rw [←he]
  exact sum_le_sum hfiber

lemma count_le_recording_card_mul {α ρ : Type*} (s : Finset α) (records : Finset ρ)
    (record : α→ρ) (hrecord : ∀a∈s,record a∈records)
    (N : ℕ) (hfiber : ∀R∈records,(s.filter (fun a=>record a=R)).card≤N) :
    s.card≤records.card*N := by
  simpa using count_le_recording_sum s records record hrecord (fun _=>N) hfiber

end WP.Critical.ShortConfiguration
