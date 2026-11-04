import WPFormalization.RandomGeometry.PantsCutStar
import WPFormalization.RandomGeometry.PantsCutGraph

/-! Recover the actual disjoint cusp pairs from a stable pants cut. -/
noncomputable section
namespace WP.RandomGeometry
open WP.External
variable {n r : ℕ} (D : MulticurveCutData n r)
    (leaf : Fin r → Fin D.components) (hleaf : ∀ e, PantsLeafData D e (leaf e))

def pantsLeafPair (e : Fin r) : Fin 2 ≃o (D.cuspSet {leaf e}) :=
  (D.cuspSet {leaf e}).orderIsoOfFin (hleaf e).two_cusps

lemma pantsLeafPair_vertex (e : Fin r) (j : Fin 2) :
    D.cuspVertex (pantsLeafPair D leaf hleaf e j) = leaf e := by
  have hm := (pantsLeafPair D leaf hleaf e j).property
  simpa only [MulticurveCutData.cuspSet, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_singleton] using hm

/-- Ordered curve slots, each carrying the increasing pair of its actual cusp
labels; injectivity is a consequence of distinct component fibers. -/
def pantsCutLabels : PantsLabels n r := by
  classical
  let f : Fin r × Fin 2 → Fin n := fun p => pantsLeafPair D leaf hleaf p.1 p.2
  have hf : Function.Injective f := by
    rintro ⟨i,a⟩ ⟨j,b⟩ he
    have hij : i = j := pantsLeaf_injective D leaf hleaf (by
      calc
        leaf i = D.cuspVertex (f (i,a)) := (pantsLeafPair_vertex D leaf hleaf i a).symm
        _ = D.cuspVertex (f (j,b)) := congrArg D.cuspVertex he
        _ = leaf j := pantsLeafPair_vertex D leaf hleaf j b)
    subst j
    have hab : a = b := (pantsLeafPair D leaf hleaf i).injective (Subtype.ext he)
    subst b
    rfl
  exact ⟨⟨f,hf⟩,fun i => (pantsLeafPair D leaf hleaf i).strictMono (show (0 : Fin 2) < 1 from by decide)⟩

@[simp] lemma pantsCutLabels_apply (e : Fin r) (j : Fin 2) :
    (pantsCutLabels D leaf hleaf).val (e,j) = pantsLeafPair D leaf hleaf e j := rfl

lemma pantsCutLabels_vertex (e : Fin r) (j : Fin 2) :
    D.cuspVertex ((pantsCutLabels D leaf hleaf).val (e,j)) = leaf e :=
  pantsLeafPair_vertex D leaf hleaf e j

lemma pantsCutLabels_covers_leaf (e : Fin r) (j : Fin n)
    (hj : D.cuspVertex j = leaf e) :
    ∃ a : Fin 2, (pantsCutLabels D leaf hleaf).val (e,a) = j := by
  have hm : j ∈ D.cuspSet {leaf e} := by simp [MulticurveCutData.cuspSet,hj]
  refine ⟨(pantsLeafPair D leaf hleaf e).symm ⟨j,hm⟩,?_⟩
  exact congrArg Subtype.val ((pantsLeafPair D leaf hleaf e).apply_symm_apply ⟨j,hm⟩)

lemma pantsCutGraph_cusp_pair (g n r : ℕ) (f : PantsLabels n r) (p : Fin r × Fin 2) :
    (pantsCutGraph g n r f).cuspVertex (f.val p) = p.1.succ := by
  classical
  have hx : ∃q : Fin r × Fin 2, f.val q = f.val p := ⟨p,rfl⟩
  change (if h : ∃q : Fin r × Fin 2, f.val q = f.val p then h.choose.1.succ else 0) = _
  rw [dif_pos hx]
  exact congrArg (fun q : Fin r × Fin 2 => q.1.succ) (f.val.injective hx.choose_spec)

lemma pantsCutGraph_no_oneHandle (g n r : ℕ) (f : PantsLabels n r) (hg : 2 ≤ g)
    (e : Fin r) : ¬ (pantsCutGraph g n r f).HasOneHandleSide e := by
  classical
  let D := pantsCutGraph g n r f
  rintro ⟨U,hs,hgU,hc⟩
  have hnotleaf : ∀i : Fin r, i.succ ∉ U := by
    intro i hi
    have hm : f.val (i,0) ∈ D.cuspSet U := by
      simp only [MulticurveCutData.cuspSet, Finset.mem_filter, Finset.mem_univ, true_and]
      change (pantsCutGraph g n r f).cuspVertex (f.val (i,0)) ∈ U
      rw [pantsCutGraph_cusp_pair]
      exact hi
    rw [hc] at hm
    simp at hm
  let z : Fin D.components := ⟨0, by change 0 < r+1; omega⟩
  have hsub : U ⊆ {z} := by
    intro c hc
    apply Finset.mem_singleton.mpr
    have hcases : c = z ∨ ∃i : Fin r, c = i.succ := by
      change (c : Fin (r+1)) = (0 : Fin (r+1)) ∨ ∃i : Fin r, c = i.succ
      exact Fin.cases (Or.inl rfl) (fun i => Or.inr ⟨i,rfl⟩) c
    rcases hcases with h | ⟨i,h⟩
    · exact h
    · exact (hnotleaf i (h ▸ hc)).elim
  have hU : U = {z} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    rcases hs.1 with ⟨c,hc⟩
    have he : c = z := Finset.mem_singleton.mp (hsub hc)
    exact ⟨he ▸ hc,fun j hj => Finset.mem_singleton.mp (hsub hj)⟩
  rw [hU] at hgU
  change (∑c ∈ ({z} : Finset (Fin D.components)), D.genus c) + _ + 1 = _ + 1 at hgU
  simp only [Finset.sum_singleton, Finset.card_singleton] at hgU
  have hroot : D.genus z = g := by simp [D,pantsCutGraph,z]
  omega

lemma pantsCutGraph_oneHandleCount (g n r : ℕ) (f : PantsLabels n r) (hg : 2 ≤ g) :
    (pantsCutGraph g n r f).oneHandleCount = 0 := by
  classical
  simp [MulticurveCutData.oneHandleCount, pantsCutGraph_no_oneHandle g n r f hg]

end WP.RandomGeometry
