import WPFormalization.RandomGeometry.GeneralPlanarStarCut

/-! Actual original cusp slots and edge sides of a general planar star. -/
noncomputable section
namespace WP.RandomGeometry
open WP.External

lemma generalPlanarStarCut_edge_leaf_iff (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (e : Fin r) (p : Fin r × Fin 2) :
    (generalPlanarStarCut g n r k f).edgeVertex p = e.succ ↔ p=(e,1) := by
  rcases p with ⟨i,j⟩
  change (if j=0 then (0 : Fin (r+1)) else i.succ)=e.succ ↔ (i,j)=(e,1)
  fin_cases j
  · change (0 : Fin (r+1))=e.succ ↔ (i,(0 : Fin 2))=(e,1)
    simp only [Prod.mk.injEq,show (0:Fin 2) ≠ 1 by decide,and_false,iff_false]
    exact (Fin.succ_ne_zero e).symm
  · change i.succ=e.succ ↔ (i,(1 : Fin 2))=(e,1)
    simp

def generalPlanarStarLeafCuspEquiv (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (e : Fin r) :
    Fin (k e) ≃ {j : Fin n // (generalPlanarStarCut g n r k f).cuspVertex j=e.succ} := by
  let a : Fin (k e) → {j : Fin n // (generalPlanarStarCut g n r k f).cuspVertex j=e.succ} :=
    fun j => ⟨f.val ⟨e,j⟩,generalPlanarStarCut_cusp_apply g n r k f ⟨e,j⟩⟩
  apply Equiv.ofBijective a
  constructor
  · intro i j hij
    exact eq_of_heq (Sigma.mk.inj_iff.mp (f.val.injective (congrArg Subtype.val hij))).2
  · intro j
    obtain ⟨a,ha⟩ := (generalPlanarStarCut_cusp_leaf_iff g n r k f e j.val).1 j.property
    exact ⟨a,Subtype.ext ha⟩

def generalPlanarStarLeafEdgeEquiv (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (e : Fin r) :
    Unit ≃ {p : Fin r × Fin 2 // (generalPlanarStarCut g n r k f).edgeVertex p=e.succ} where
  toFun _ := ⟨(e,1),by simp [generalPlanarStarCut]⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv p := Subtype.ext ((generalPlanarStarCut_edge_leaf_iff g n r k f e p.val).1 p.property).symm

/-- The leaf boundary retains its k_e labeled cusps and its one physical edge. -/
def generalPlanarStarLeafBoundaryEquiv (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (e : Fin r) :
    (Fin (k e) ⊕ Unit) ≃ (generalPlanarStarCut g n r k f).Boundary e.succ :=
  Equiv.sumCongr (generalPlanarStarLeafCuspEquiv g n r k f e)
    (generalPlanarStarLeafEdgeEquiv g n r k f e)

lemma generalPlanarStarCut_leaf_boundaryCount (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (e : Fin r) :
    (generalPlanarStarCut g n r k f).boundaryCount e.succ = k e+1 := by
  classical
  letI : Fintype ((generalPlanarStarCut g n r k f).Boundary e.succ) :=
    MulticurveCutData.instFintypeBoundary (generalPlanarStarCut g n r k f) e.succ
  change Fintype.card ((generalPlanarStarCut g n r k f).Boundary e.succ) = k e+1
  calc
    _ = Fintype.card (Fin (k e) ⊕ Unit) :=
      (Fintype.card_congr (generalPlanarStarLeafBoundaryEquiv g n r k f e)).symm
    _ = k e+1 := by simp

def generalPlanarStarRootEdgeEquiv (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) :
    Fin r ≃ {p : Fin r × Fin 2 //
      (generalPlanarStarCut g n r k f).edgeVertex p=(0 : Fin (r+1))} where
  toFun e := ⟨(e,0),by simp [generalPlanarStarCut]⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    have hj : p.val.2=0 := by
      by_contra hj
      have h := p.property
      simp [generalPlanarStarCut,hj] at h
    exact Prod.ext rfl hj.symm

lemma generalPlanarStarCut_root_cusp_card (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) :
    Nat.card {j : Fin n // (generalPlanarStarCut g n r k f).cuspVertex j=(0 : Fin (r+1))} =
      n - ∑ i, k i := by
  classical
  have he := Equiv.subtypeEquivRight (generalPlanarStarCut_cusp_root_iff g n r k f)
  rw [Nat.card_congr he,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  have hc : Fintype.card {j : Fin n // ∃p : Σ i : Fin r, Fin (k i), f.val p=j} = ∑ i, k i := by
    let e : (Σ i : Fin r, Fin (k i)) ≃ {j : Fin n // ∃p : Σ i : Fin r, Fin (k i), f.val p=j} :=
      Equiv.ofInjective f.val f.val.injective
    simpa only [Fintype.card_sigma,Fintype.card_fin] using (Fintype.card_congr e).symm
  rw [hc,Fintype.card_fin]

def generalPlanarStarRootCuspEquiv (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) :
    Fin (n-∑ i,k i) ≃ {j : Fin n //
      (generalPlanarStarCut g n r k f).cuspVertex j=(0 : Fin (r+1))} := by
  classical
  have hc : Fintype.card {j : Fin n //
      (generalPlanarStarCut g n r k f).cuspVertex j=(0 : Fin (r+1))}=n-∑ i,k i := by
    simpa only [Nat.card_eq_fintype_card] using generalPlanarStarCut_root_cusp_card g n r k f
  exact (finCongr hc.symm).trans (Fintype.equivFin _).symm

/-- All unused original cusps remain at the root, together with one edge side
for each ordered curve. -/
def generalPlanarStarRootBoundaryEquiv (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) :
    (Fin (n-∑ i,k i) ⊕ Fin r) ≃
      (generalPlanarStarCut g n r k f).Boundary (0 : Fin (r+1)) :=
  Equiv.sumCongr (generalPlanarStarRootCuspEquiv g n r k f)
    (generalPlanarStarRootEdgeEquiv g n r k f)

lemma generalPlanarStarCut_root_boundaryCount (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) :
    (generalPlanarStarCut g n r k f).boundaryCount (0 : Fin (r+1)) = n-(∑ i,k i)+r := by
  classical
  letI : Fintype ((generalPlanarStarCut g n r k f).Boundary (0 : Fin (r+1))) :=
    MulticurveCutData.instFintypeBoundary (generalPlanarStarCut g n r k f) (0 : Fin (r+1))
  change Fintype.card ((generalPlanarStarCut g n r k f).Boundary (0 : Fin (r+1))) = n-(∑ i,k i)+r
  calc
    _ = Fintype.card (Fin (n-∑ i,k i) ⊕ Fin r) :=
      (Fintype.card_congr (generalPlanarStarRootBoundaryEquiv g n r k f)).symm
    _ = n-(∑ i,k i)+r := by simp

end WP.RandomGeometry
