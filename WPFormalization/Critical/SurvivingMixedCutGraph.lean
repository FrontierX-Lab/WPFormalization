import WPFormalization.RandomGeometry.PantsStarTopology
import WPFormalization.RandomGeometry.PantsStarLabels
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace WP.Critical
open WP.External WP.RandomGeometry Finset
open scoped Classical

/-- The actual surviving graph has r ordered two-cusp leaves and k ordered
loops at its large root, whose genus drops from g to g-k. -/
def survivingMixedCutGraph (g n r k : ℕ) (f : PantsLabels n r) : MulticurveCutData n (r+k) where
  components := r+1
  genus c := if c=0 then g-k else 0
  cuspVertex := (pantsCutGraph (g-k) n r f).cuspVertex
  edgeVertex e := Fin.addCases (fun i => if e.2=0 then 0 else i.succ) (fun _ => 0) e.1

lemma survivingMixed_root_fixed (g n r k : ℕ) (f : PantsLabels n r) (hg : k < g)
    (v : Equiv.Perm (Fin (r+1)))
    (hv : ∀ c, (survivingMixedCutGraph g n r k f).genus (v c)=
      (survivingMixedCutGraph g n r k f).genus c) : v 0=0 :=
  pantsCutGraph_root_fixed (g-k) n r f (by omega) v hv

lemma survivingMixed_flip_iff (g n r k : ℕ) (f : PantsLabels n r) (hg : k < g)
    (b : Fin (r+k) → Bool) :
    (survivingMixedCutGraph g n r k f).FlipPreserves b ↔ ∀ i : Fin r, b (i.castAdd k)=false := by
  constructor
  · rintro ⟨v,hv,hc,he⟩ i
    have hv0 := survivingMixed_root_fixed g n r k f hg v hv
    have hi := he (i.castAdd k) 0
    cases hb : b (i.castAdd k)
    · rfl
    · have hh : v (0 : Fin (r+1))=i.succ := by simpa [survivingMixedCutGraph,hb] using hi
      exact (Fin.succ_ne_zero i (hv0.symm.trans hh).symm).elim
  · intro hb
    refine ⟨Equiv.refl _,fun _ => rfl,fun _ => rfl,?_⟩
    intro e j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) e
    · simp [survivingMixedCutGraph,hb i] <;> rfl
    · simp [survivingMixedCutGraph] <;> rfl

/-- Pants edges admit no side flip; the k loop sides may be flipped independently. -/
def survivingMixedFlipEquiv (g n r k : ℕ) (f : PantsLabels n r) (hg : k < g) :
    {b : Fin (r+k) → Bool // (survivingMixedCutGraph g n r k f).FlipPreserves b} ≃
      (Fin k → Bool) where
  toFun b i := b.val (Fin.natAdd r i)
  invFun b := ⟨Fin.append (fun _ : Fin r => false) b,
    (survivingMixed_flip_iff g n r k f hg _).mpr (by simp)⟩
  left_inv b := by
    apply Subtype.ext
    funext e
    refine Fin.addCases (fun i => ?_) (fun i => ?_) e
    · simpa using ((survivingMixed_flip_iff g n r k f hg b.val).mp b.property i).symm
    · simp
  right_inv b := by funext i; simp

lemma survivingMixed_orientation_index (g n r k : ℕ) (f : PantsLabels n r) (hg : k < g) :
    (survivingMixedCutGraph g n r k f).orientationStabilizerIndex=2^k := by
  unfold MulticurveCutData.orientationStabilizerIndex
  rw [Nat.card_congr (survivingMixedFlipEquiv g n r k f hg),Nat.card_eq_fintype_card]
  simp

lemma survivingMixed_euler (g n r k : ℕ) (f : PantsLabels n r) (hg : k ≤ g) :
    (∑ c, (survivingMixedCutGraph g n r k f).genus c)+(r+k)+1=
      g+(survivingMixedCutGraph g n r k f).components := by
  have hs : (∑ c, (survivingMixedCutGraph g n r k f).genus c)=g-k := by
    change (∑ c : Fin (r+1), if c=(0 : Fin (r+1)) then g-k else 0)=g-k
    simp [Fin.sum_univ_succ]
  rw [hs]
  change g-k+(r+k)+1=g+(r+1)
  omega

lemma survivingMixed_connected (g n r k : ℕ) (f : PantsLabels n r) :
    (survivingMixedCutGraph g n r k f).ConnectedWithin univ := by
  classical
  let D := survivingMixedCutGraph g n r k f
  letI : NeZero D.components := ⟨by change r+1≠0; omega⟩
  let root : Fin D.components := 0
  have ha (i : Fin r) : D.AdjacentWithin univ root i.succ := by
    refine ⟨mem_univ _,mem_univ _,i.castAdd k,Or.inl ?_⟩
    constructor <;> simp [D,survivingMixedCutGraph,root]
  have hb (i : Fin r) : D.AdjacentWithin univ i.succ root := by
    refine ⟨mem_univ _,mem_univ _,i.castAdd k,Or.inr ?_⟩
    constructor <;> simp [D,survivingMixedCutGraph,root]
  have hf (c : Fin D.components) : Relation.ReflTransGen (D.AdjacentWithin univ) root c :=
    Fin.cases Relation.ReflTransGen.refl (fun i => Relation.ReflTransGen.single (ha i)) c
  have hg (c : Fin D.components) : Relation.ReflTransGen (D.AdjacentWithin univ) c root :=
    Fin.cases Relation.ReflTransGen.refl (fun i => Relation.ReflTransGen.single (hb i)) c
  exact ⟨⟨root,mem_univ _⟩,fun a _ b _ => (hg a).trans (hf b)⟩

lemma survivingMixed_no_handle_side (g n r k : ℕ) (f : PantsLabels n r) (hg : k+2 ≤ g)
    (e : Fin (r+k)) : ¬ (survivingMixedCutGraph g n r k f).HasOneHandleSide e := by
  classical
  let D := survivingMixedCutGraph g n r k f
  letI : NeZero D.components := ⟨by change r+1≠0; omega⟩
  rintro ⟨U,hside,hgen,hcusps⟩
  have hleaf (i : Fin r) : i.succ ∉ U := by
    intro hi
    have hc : f.val (i,0) ∈ D.cuspSet U := by
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      change (pantsCutGraph (g-k) n r f).cuspVertex (f.val (i,0)) ∈ U
      rw [pantsCutGraph_cusp_pair]
      exact hi
    rw [hcusps] at hc
    exact Finset.notMem_empty _ hc
  have hsub : U ⊆ {0} := by
    intro c
    exact Fin.cases (fun _ => mem_singleton_self 0) (fun i hi => (hleaf i hi).elim) c
  have hroot : (0 : Fin (r+1)) ∈ U := by
    obtain ⟨c,hc⟩ := hside.1
    have he : c=0 := mem_singleton.mp (hsub hc)
    exact he ▸ hc
  have hU : U={0} := Subset.antisymm hsub (singleton_subset_iff.mpr hroot)
  change (∑ c ∈ U,D.genus c)+(D.internalEdges U).card+1=U.card+1 at hgen
  rw [hU,sum_singleton,card_singleton] at hgen
  change g-k+(D.internalEdges {0}).card+1=1+1 at hgen
  omega

lemma survivingMixed_oneHandleCount (g n r k : ℕ) (f : PantsLabels n r) (hg : k+2 ≤ g) :
    (survivingMixedCutGraph g n r k f).oneHandleCount=0 := by
  classical
  simp only [MulticurveCutData.oneHandleCount,
    filter_eq_empty_iff.mpr (fun e _ => survivingMixed_no_handle_side g n r k f hg e),card_empty]
end WP.Critical
