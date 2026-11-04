import WPFormalization.RandomGeometry.PantsCutLabels

/-! The original cusp labels distinguish the ordered pants-star orbits. -/
noncomputable section
namespace WP.RandomGeometry
open WP.External

lemma pantsStar_leaf_cusp_exists (g n r : ℕ) (f : PantsLabels n r)
    (i : Fin r) (j : Fin n) (hj : (pantsCutGraph g n r f).cuspVertex j = i.succ) :
    ∃a : Fin 2, f.val (i,a)=j := by
  classical
  by_cases h : ∃p : Fin r × Fin 2, f.val p=j
  · rcases h with ⟨p,hp⟩
    rw [←hp,pantsCutGraph_cusp_pair] at hj
    have hi : p.1=i := Fin.succ_injective _ hj
    exact ⟨p.2,by simpa only [←hi] using hp⟩
  · have hz : (pantsCutGraph g n r f).cuspVertex j = (0 : Fin (r+1)) := by
      change (if h : ∃p : Fin r × Fin 2, f.val p=j then h.choose.1.succ else 0)=_
      rw [dif_neg h]
    exact (Fin.succ_ne_zero i (hj.symm.trans hz)).elim

lemma pantsLabels_eq_of_row_cover {n r : ℕ} (f q : PantsLabels n r)
    (h : ∀i j, ∃a : Fin 2, q.val (i,a)=f.val (i,j)) : f=q := by
  apply Subtype.ext
  apply Function.Embedding.ext
  rintro ⟨i,j⟩
  obtain ⟨a,ha⟩ := h i 0
  obtain ⟨b,hb⟩ := h i 1
  have hf := f.property i
  have hq := q.property i
  have hp : f.val (i,0)=q.val (i,0) ∧ f.val (i,1)=q.val (i,1) := by
    fin_cases a <;> fin_cases b <;> simp_all <;> omega
  fin_cases j
  · exact hp.1
  · exact hp.2

set_option backward.isDefEq.respectTransparency false in
lemma pantsStar_isomorphism_labels (g n r : ℕ) (f q : PantsLabels n r) (hg : 0 < g)
    (I : MulticurveCutData.Isomorphism (pantsCutGraph g n r f) (pantsCutGraph g n r q)) :
    f=q := by
  classical
  let v : Fin (r+1) ≃ Fin (r+1) := I.vertexEquiv
  have hv0 : v (0 : Fin (r+1))=0 := by
    have hh := I.genus_eq (0 : Fin (r+1))
    by_contra hn
    have he : v (0 : Fin (r+1)) ≠ 0 := hn
    change (if v 0=0 then g else 0)=g at hh
    rw [if_neg he] at hh
    omega
  have hflip : ∀i, I.flip i=false := by
    intro i
    cases hi : I.flip i
    · rfl
    · have hh : v (0 : Fin (r+1))=i.succ := by
        simpa [pantsCutGraph,v,hi] using I.edge_eq i 0
      exact (Fin.succ_ne_zero i (hv0.symm.trans hh).symm).elim
  have hvleaf (i : Fin r) : v i.succ=i.succ := by
    simpa [pantsCutGraph,v,hflip i] using I.edge_eq i 1
  apply pantsLabels_eq_of_row_cover f q
  intro i j
  apply pantsStar_leaf_cusp_exists g n r q i (f.val (i,j))
  have hh := I.cusp_eq (f.val (i,j))
  rw [pantsCutGraph_cusp_pair] at hh
  exact hh.symm.trans (hvleaf i)

end WP.RandomGeometry
