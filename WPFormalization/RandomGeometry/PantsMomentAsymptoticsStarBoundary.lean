import WPFormalization.RandomGeometry.PantsCutLabels

/-! Exact canonical-star boundary slots and counts. -/
noncomputable section
namespace WP.RandomGeometry
open WP.External

lemma pantsStar_cusp_root_iff (g n r : ℕ) (f : PantsLabels n r) (j : Fin n) :
    (pantsCutGraph g n r f).cuspVertex j = (0 : Fin (r+1)) ↔ ¬∃p : Fin r × Fin 2, f.val p=j := by
  classical
  by_cases hj : ∃p : Fin r × Fin 2, f.val p=j
  · rcases hj with ⟨p,rfl⟩
    rw [pantsCutGraph_cusp_pair]
    constructor
    · intro h
      exact (Fin.succ_ne_zero _ h).elim
    · intro h
      exact (h ⟨p,rfl⟩).elim
  · simp [pantsCutGraph,hj]

lemma pantsStar_cusp_leaf_iff (g n r : ℕ) (f : PantsLabels n r) (e : Fin r) (j : Fin n) :
    (pantsCutGraph g n r f).cuspVertex j = e.succ ↔ ∃a : Fin 2, f.val (e,a)=j := by
  classical
  constructor
  · intro hj
    by_cases hrange : ∃p : Fin r × Fin 2, f.val p=j
    · rcases hrange with ⟨p,rfl⟩
      rw [pantsCutGraph_cusp_pair] at hj
      have he : p.1=e := Fin.succ_injective _ hj
      exact ⟨p.2,by rw [←he]⟩
    · have hzero := (pantsStar_cusp_root_iff g n r f j).2 hrange
      rw [hzero] at hj
      exact (Fin.succ_ne_zero e hj.symm).elim
  · rintro ⟨a,rfl⟩
    exact pantsCutGraph_cusp_pair g n r f (e,a)

lemma pantsStar_edge_leaf_iff (g n r : ℕ) (f : PantsLabels n r)
    (e : Fin r) (p : Fin r × Fin 2) :
    (pantsCutGraph g n r f).edgeVertex p = e.succ ↔ p=(e,1) := by
  rcases p with ⟨i,j⟩
  change (if j=0 then (0 : Fin (r+1)) else i.succ)=e.succ ↔ (i,j)=(e,1)
  fin_cases j
  · change (0 : Fin (r+1))=e.succ ↔ (i,(0 : Fin 2))=(e,1)
    simp only [Prod.mk.injEq,show (0:Fin 2) ≠ 1 by decide,and_false,iff_false]
    exact (Fin.succ_ne_zero e).symm
  · change i.succ=e.succ ↔ (i,(1 : Fin 2))=(e,1)
    simp

/-- The two original cusp slots of a canonical leaf. -/
def pantsStarLeafCuspEquiv (g n r : ℕ) (f : PantsLabels n r) (e : Fin r) :
    Fin 2 ≃ {j : Fin n // (pantsCutGraph g n r f).cuspVertex j=e.succ} := by
  let a : Fin 2 → {j : Fin n // (pantsCutGraph g n r f).cuspVertex j=e.succ} :=
    fun j => ⟨f.val (e,j),pantsCutGraph_cusp_pair g n r f (e,j)⟩
  apply Equiv.ofBijective a
  constructor
  · intro i j hij
    exact congrArg Prod.snd (f.val.injective (congrArg Subtype.val hij))
  · intro j
    obtain ⟨a,ha⟩ := (pantsStar_cusp_leaf_iff g n r f e j.val).1 j.property
    exact ⟨a,Subtype.ext ha⟩

/-- A canonical leaf has just its one cut-edge slot. -/
def pantsStarLeafEdgeEquiv (g n r : ℕ) (f : PantsLabels n r) (e : Fin r) :
    Unit ≃ {p : Fin r × Fin 2 // (pantsCutGraph g n r f).edgeVertex p=e.succ} where
  toFun _ := ⟨(e,1),by simp [pantsCutGraph]⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv p := Subtype.ext ((pantsStar_edge_leaf_iff g n r f e p.val).1 p.property).symm

lemma pantsStar_leaf_boundaryCount (g n r : ℕ) (f : PantsLabels n r) (e : Fin r) :
    (pantsCutGraph g n r f).boundaryCount e.succ = 3 := by
  classical
  let e' : (Fin 2 ⊕ Unit) ≃ (pantsCutGraph g n r f).Boundary e.succ :=
    Equiv.sumCongr (pantsStarLeafCuspEquiv g n r f e) (pantsStarLeafEdgeEquiv g n r f e)
  letI : Fintype ((pantsCutGraph g n r f).Boundary e.succ) :=
    MulticurveCutData.instFintypeBoundary (pantsCutGraph g n r f) e.succ
  change Fintype.card ((pantsCutGraph g n r f).Boundary e.succ) = 3
  calc
    _ = Fintype.card (Fin 2 ⊕ Unit) := (Fintype.card_congr e').symm
    _ = 3 := by simp

/-- At the root each edge contributes precisely its zero-side slot. -/
def pantsStarRootEdgeEquiv (g n r : ℕ) (f : PantsLabels n r) :
    Fin r ≃ {p : Fin r × Fin 2 // (pantsCutGraph g n r f).edgeVertex p=(0 : Fin (r+1))} where
  toFun e := ⟨(e,0),by simp [pantsCutGraph]⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    have hj : p.val.2=0 := by
      by_contra hj
      have h := p.property
      simp [pantsCutGraph,hj] at h
    exact Prod.ext rfl hj.symm

lemma pantsStar_root_cusp_card (g n r : ℕ) (f : PantsLabels n r) :
    Nat.card {j : Fin n // (pantsCutGraph g n r f).cuspVertex j=(0 : Fin (r+1))} = n-2*r := by
  classical
  have he := Equiv.subtypeEquivRight (pantsStar_cusp_root_iff g n r f)
  rw [Nat.card_congr he,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  have hc : Fintype.card {j : Fin n // ∃p : Fin r × Fin 2, f.val p=j} = 2*r := by
    let e : (Fin r × Fin 2) ≃ {j : Fin n // ∃p : Fin r × Fin 2, f.val p=j} :=
      Equiv.ofInjective f.val f.val.injective
    simpa only [Fintype.card_prod,Fintype.card_fin,mul_comm] using (Fintype.card_congr e).symm
  rw [hc,Fintype.card_fin]

/-- Root cusp slots carry no physical length. The equivalence retains every
remaining original cusp, instead of silently dropping it. -/
def pantsStarRootCuspEquiv (g n r : ℕ) (f : PantsLabels n r) :
    Fin (n-2*r) ≃ {j : Fin n // (pantsCutGraph g n r f).cuspVertex j=(0 : Fin (r+1))} :=
  by
    classical
    have hc : Fintype.card {j : Fin n // (pantsCutGraph g n r f).cuspVertex j=(0 : Fin (r+1))}=n-2*r := by
      simpa only [Nat.card_eq_fintype_card] using pantsStar_root_cusp_card g n r f
    exact (finCongr hc.symm).trans (Fintype.equivFin _).symm

lemma pantsStar_root_boundaryCount (g n r : ℕ) (f : PantsLabels n r) (hn : 2*r ≤ n) :
    (pantsCutGraph g n r f).boundaryCount (0 : Fin (r+1)) = n-r := by
  classical
  let e' : (Fin (n-2*r) ⊕ Fin r) ≃ (pantsCutGraph g n r f).Boundary (0 : Fin (r+1)) :=
    Equiv.sumCongr (pantsStarRootCuspEquiv g n r f) (pantsStarRootEdgeEquiv g n r f)
  letI : Fintype ((pantsCutGraph g n r f).Boundary (0 : Fin (r+1))) :=
    MulticurveCutData.instFintypeBoundary (pantsCutGraph g n r f) (0 : Fin (r+1))
  change Fintype.card ((pantsCutGraph g n r f).Boundary (0 : Fin (r+1))) = n-r
  calc
    _ = Fintype.card (Fin (n-2*r) ⊕ Fin r) := (Fintype.card_congr e').symm
    _ = n-r := by simp; omega


lemma pantsStar_genus_sum (g n r : ℕ) (f : PantsLabels n r) :
    (∑ c, (pantsCutGraph g n r f).genus c) = g := by
  change (∑ c : Fin (r+1), if c=(0 : Fin (r+1)) then g else 0) = g
  simp [Fin.sum_univ_succ]

end WP.RandomGeometry
