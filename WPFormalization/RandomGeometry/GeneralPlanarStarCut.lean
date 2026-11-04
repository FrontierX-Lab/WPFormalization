import WPFormalization.External.MulticurveCutData
import WPFormalization.RandomGeometry.PlanarLabelBlocks

/-! Canonical planar stars with ordered edges and arbitrary cusp-block sizes. -/
noncomputable section
namespace WP.RandomGeometry
open WP.External

def generalPlanarStarCut (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) : MulticurveCutData n r where
  components := r + 1
  genus c := if c = 0 then g else 0
  cuspVertex j := by
    classical
    exact if h : ∃ p : Σ i : Fin r, Fin (k i), f.val p = j then h.choose.1.succ else 0
  edgeVertex p := if p.2 = 0 then 0 else p.1.succ

lemma generalPlanarStarCut_cusp_apply (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (p : Σ i : Fin r, Fin (k i)) :
    (generalPlanarStarCut g n r k f).cuspVertex (f.val p) = p.1.succ := by
  classical
  have hx : ∃ q : Σ i : Fin r, Fin (k i), f.val q = f.val p := ⟨p,rfl⟩
  change (if h : ∃ q : Σ i : Fin r, Fin (k i), f.val q = f.val p
    then h.choose.1.succ else 0) = _
  rw [dif_pos hx]
  exact congrArg (fun q : Σ i : Fin r, Fin (k i) => q.1.succ) (f.val.injective hx.choose_spec)

lemma generalPlanarStarCut_cusp_root_iff (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (j : Fin n) :
    (generalPlanarStarCut g n r k f).cuspVertex j = (0 : Fin (r+1)) ↔
      ¬ ∃ p : Σ i : Fin r, Fin (k i), f.val p = j := by
  classical
  by_cases hj : ∃ p : Σ i : Fin r, Fin (k i), f.val p = j
  · rcases hj with ⟨p,rfl⟩
    rw [generalPlanarStarCut_cusp_apply]
    constructor
    · intro h; exact (Fin.succ_ne_zero _ h).elim
    · intro h; exact (h ⟨p,rfl⟩).elim
  · simp [generalPlanarStarCut,hj]

lemma generalPlanarStarCut_cusp_leaf_iff (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (i : Fin r) (j : Fin n) :
    (generalPlanarStarCut g n r k f).cuspVertex j = i.succ ↔
      ∃ a : Fin (k i), f.val ⟨i,a⟩ = j := by
  classical
  constructor
  · intro hj
    by_cases hrange : ∃ p : Σ i : Fin r, Fin (k i), f.val p = j
    · rcases hrange with ⟨p,rfl⟩
      rw [generalPlanarStarCut_cusp_apply] at hj
      have hi : p.1 = i := Fin.succ_injective _ hj
      subst i
      exact ⟨p.2,rfl⟩
    · have hzero := (generalPlanarStarCut_cusp_root_iff g n r k f j).mpr hrange
      rw [hzero] at hj
      exact (Fin.succ_ne_zero i hj.symm).elim
  · rintro ⟨a,rfl⟩
    exact generalPlanarStarCut_cusp_apply g n r k f ⟨i,a⟩

set_option backward.isDefEq.respectTransparency false in
lemma generalPlanarStarCut_cuspSet_leaf (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (i : Fin r) :
    (generalPlanarStarCut g n r k f).cuspSet {i.succ} = f.labelSet i := by
  classical
  ext j
  simp only [MulticurveCutData.cuspSet, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  exact (generalPlanarStarCut_cusp_leaf_iff g n r k f i j).trans (f.mem_labelSet i j).symm

lemma generalPlanarStarCut_root_fixed (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (hg : 0 < g) (v : Equiv.Perm (Fin (r+1)))
    (hv : ∀ c, (generalPlanarStarCut g n r k f).genus (v c) =
      (generalPlanarStarCut g n r k f).genus c) : v 0 = 0 := by
  have he := hv 0
  by_contra h
  simp only [generalPlanarStarCut, h, if_false, if_true] at he
  omega

lemma generalPlanarStarCut_flip_eq_false (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (hg : 0 < g) (b : Fin r → Bool)
    (hb : (generalPlanarStarCut g n r k f).FlipPreserves b) : b = fun _ => false := by
  rcases hb with ⟨v,hv,_,he⟩
  have hv0 := generalPlanarStarCut_root_fixed g n r k f hg v hv
  funext i
  have h := he i 0
  cases hb : b i
  · rfl
  · have heq : v (0 : Fin (r+1)) = i.succ := by
      simpa [generalPlanarStarCut,hb] using h
    exact (Fin.succ_ne_zero i (hv0.symm.trans heq).symm).elim

lemma generalPlanarStarCut_orientation_index (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (hg : 0 < g) :
    (generalPlanarStarCut g n r k f).orientationStabilizerIndex = 1 := by
  classical
  unfold MulticurveCutData.orientationStabilizerIndex
  have hd : (generalPlanarStarCut g n r k f).FlipPreserves (fun _ => false) := by
    refine ⟨Equiv.refl _, ?_, ?_, ?_⟩ <;> simp
  letI : Unique {b : Fin r → Bool // (generalPlanarStarCut g n r k f).FlipPreserves b} :=
    ⟨⟨fun _ => false, hd⟩, fun b => Subtype.ext
      (generalPlanarStarCut_flip_eq_false g n r k f hg b.val b.property)⟩
  exact Nat.card_unique

lemma generalPlanarStarCut_connected (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) :
    (generalPlanarStarCut g n r k f).ConnectedWithin Finset.univ := by
  classical
  let D := generalPlanarStarCut g n r k f
  let root : Fin D.components := ⟨0,by change 0 < r+1; omega⟩
  have hadj (i : Fin r) : D.AdjacentWithin Finset.univ root i.succ := by
    refine ⟨Finset.mem_univ _,Finset.mem_univ _,i,Or.inl ?_⟩
    constructor <;> simp [D,generalPlanarStarCut,root]
  have hadj' (i : Fin r) : D.AdjacentWithin Finset.univ i.succ root := by
    refine ⟨Finset.mem_univ _,Finset.mem_univ _,i,Or.inr ?_⟩
    constructor <;> simp [D,generalPlanarStarCut,root]
  have hr (c : Fin D.components) :
      Relation.ReflTransGen (D.AdjacentWithin Finset.univ) root c := by
    refine Fin.cases ?_ (fun i => Relation.ReflTransGen.single (hadj i)) c
    exact Relation.ReflTransGen.refl
  have hr' (c : Fin D.components) :
      Relation.ReflTransGen (D.AdjacentWithin Finset.univ) c root := by
    refine Fin.cases ?_ (fun i => Relation.ReflTransGen.single (hadj' i)) c
    exact Relation.ReflTransGen.refl
  refine ⟨⟨root,Finset.mem_univ _⟩,?_⟩
  intro a _ b _
  exact (hr' a).trans (hr b)

lemma generalPlanarStarCut_genus_sum (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) : (∑ c, (generalPlanarStarCut g n r k f).genus c) = g := by
  change (∑ c : Fin (r+1), if c=(0 : Fin (r+1)) then g else 0) = g
  simp [Fin.sum_univ_succ]

lemma generalPlanarStarCut_euler (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) :
    (∑ c, (generalPlanarStarCut g n r k f).genus c) + r + 1 =
      g + (generalPlanarStarCut g n r k f).components := by
  rw [generalPlanarStarCut_genus_sum]
  rfl

end WP.RandomGeometry
