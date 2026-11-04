import WPFormalization.RandomGeometry.GeneralPlanarTuplePartition
import WPFormalization.RandomGeometry.PlanarCutTreeBudget
import WPFormalization.RandomGeometry.GeneralPlanarSparsePatterns

/-! Uniform finite-pattern counting of the actual planar mapping-class orbits.
Only the actual a occupied cusp labels contribute a power n^a. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External
open scoped BigOperators
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    {g n r : ℕ} {k : Fin r → ℕ}

lemma generalPlanarOrbit_planar_sides (o : GeneralPlanarOrbit T g n r k) :
    ∀e,∃U,(T.cut o.val).IsSide e U ∧ (T.cut o.val).SideGenus U 0 := by
  intro e
  obtain ⟨S,⟨U,hU,hgen,hS⟩,_⟩ := o.property e
  exact ⟨U,hU,hgen⟩

lemma generalPlanarOrbit_sides (o : GeneralPlanarOrbit T g n r k) :
    ∀e,∃U,(T.cut o.val).IsSide e U := by
  intro e
  obtain ⟨U,hU,_⟩ := generalPlanarOrbit_planar_sides T o e
  exact ⟨U,hU⟩

def generalPlanarOrbitRoot (hg : 1≤g) (o : GeneralPlanarOrbit T g n r k) :
    Fin (T.cut o.val).components :=
  (PlanarCut.exists_unique_genus_root (T.cut o.val) hg (T.cut_connected o.val)
    (T.cut_euler o.val) (generalPlanarOrbit_planar_sides T o)).choose

lemma generalPlanarOrbitRoot_spec (hg : 1≤g) (o : GeneralPlanarOrbit T g n r k) :
    (T.cut o.val).genus (generalPlanarOrbitRoot T hg o)=g ∧
      ∀c,c≠generalPlanarOrbitRoot T hg o →(T.cut o.val).genus c=0 :=
  (PlanarCut.exists_unique_genus_root (T.cut o.val) hg (T.cut_connected o.val)
    (T.cut_euler o.val) (generalPlanarOrbit_planar_sides T o)).choose_spec

def generalPlanarOrbitVertexEquiv (hg : 1≤g) (o : GeneralPlanarOrbit T g n r k) :
    Fin (r+1) ≃ Fin (T.cut o.val).components :=
  PlanarCut.vertexEquivRoot (T.cut o.val) (T.cut_connected o.val)
    (generalPlanarOrbit_sides T o) (generalPlanarOrbitRoot T hg o)

@[simp] lemma generalPlanarOrbitVertexEquiv_zero (hg : 1≤g)
    (o : GeneralPlanarOrbit T g n r k) :
    generalPlanarOrbitVertexEquiv T hg o 0=generalPlanarOrbitRoot T hg o := by
  exact PlanarCut.vertexEquivRoot_zero _ _ _ _

lemma generalPlanarOrbit_normalized_genus (hg : 1≤g)
    (o : GeneralPlanarOrbit T g n r k) (i : Fin (r+1)) :
    (T.cut o.val).genus (generalPlanarOrbitVertexEquiv T hg o i)=if i=0 then g else 0 := by
  by_cases hi : i=0
  · subst i
    simp [generalPlanarOrbitRoot_spec T hg o]
  · rw [if_neg hi]
    apply (generalPlanarOrbitRoot_spec T hg o).2
    intro heq
    have heq' : generalPlanarOrbitVertexEquiv T hg o i=generalPlanarOrbitVertexEquiv T hg o 0 :=
      heq.trans (generalPlanarOrbitVertexEquiv_zero T hg o).symm
    exact hi ((generalPlanarOrbitVertexEquiv T hg o).injective heq')

def generalPlanarOrbitPattern (hg : 1≤g) (o : GeneralPlanarOrbit T g n r k) :
    ((Fin r × Fin 2) → Fin (r+1)) × (Fin n → Fin (r+1)) :=
  (fun p => (generalPlanarOrbitVertexEquiv T hg o).symm ((T.cut o.val).edgeVertex p),
   fun i => (generalPlanarOrbitVertexEquiv T hg o).symm ((T.cut o.val).cuspVertex i))

lemma generalPlanarOrbitPattern_injective (hg : 1≤g) :
    Function.Injective (generalPlanarOrbitPattern T (n:=n) (k:=k) hg) := by
  intro o p hop
  let E := generalPlanarOrbitVertexEquiv T hg o
  let F := generalPlanarOrbitVertexEquiv T hg p
  let V := E.symm.trans F
  have hgen : ∀c,(T.cut p.val).genus (V c)=(T.cut o.val).genus c := by
    intro c
    have h1 := generalPlanarOrbit_normalized_genus T hg p (E.symm c)
    have h2 := generalPlanarOrbit_normalized_genus T hg o (E.symm c)
    simpa only [V,E,F,Equiv.trans_apply,Equiv.apply_symm_apply] using h1.trans h2.symm
  have hcusp : ∀i,V ((T.cut o.val).cuspVertex i)=(T.cut p.val).cuspVertex i := by
    intro i
    have h := congrFun (congrArg Prod.snd hop) i
    exact (congrArg F h).trans (F.apply_symm_apply _)
  have hedge : ∀e j,V ((T.cut o.val).edgeVertex (e,j))=(T.cut p.val).edgeVertex (e,j) := by
    intro e j
    have h := congrFun (congrArg Prod.fst hop) (e,j)
    exact (congrArg F h).trans (F.apply_symm_apply _)
  apply Subtype.ext
  apply T.cut_classifies o.val p.val
  refine ⟨{vertexEquiv:=V,flip:=fun _=>false,genus_eq:=hgen,cusp_eq:=hcusp,edge_eq:=?_}⟩
  intro e j
  exact hedge e j

lemma generalPlanarOrbit_cusp_zero_iff (hg : 1≤g)
    (o : GeneralPlanarOrbit T g n r k) (i : Fin n) :
    (generalPlanarOrbitPattern T hg o).2 i=0 ↔
      (T.cut o.val).cuspVertex i=generalPlanarOrbitRoot T hg o := by
  constructor
  · intro h
    have ht := congrArg (generalPlanarOrbitVertexEquiv T hg o) h
    simpa [generalPlanarOrbitPattern] using ht
  · intro h
    change (generalPlanarOrbitVertexEquiv T hg o).symm ((T.cut o.val).cuspVertex i)=0
    rw [h,←generalPlanarOrbitVertexEquiv_zero T hg o]
    exact (generalPlanarOrbitVertexEquiv T hg o).symm_apply_apply 0

lemma generalPlanarOrbit_pattern_support_card (hg : 1≤g)
    (o : GeneralPlanarOrbit T g n r k) :
    (Finset.univ.filter (fun i => (generalPlanarOrbitPattern T hg o).2 i≠0)).card =
      PlanarCut.planarCuspCount (T.cut o.val) (generalPlanarOrbitRoot T hg o) := by
  classical
  congr 1
  ext i
  simp only [PlanarCut.planarCuspCount,PlanarCut.nonrootVertices,MulticurveCutData.cuspSet,
    Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,and_true]
  exact not_congr (generalPlanarOrbit_cusp_zero_iff T hg o i)

def GeneralPlanarOrbitAtCusps (hg : 1≤g) (a : ℕ) :=
  {o : GeneralPlanarOrbit T g n r k //
    PlanarCut.planarCuspCount (T.cut o.val) (generalPlanarOrbitRoot T hg o)=a}

instance (hg : 1≤g) (a : ℕ) : Fintype (GeneralPlanarOrbitAtCusps T (n:=n) (k:=k) hg a) := by
  classical
  unfold GeneralPlanarOrbitAtCusps
  infer_instance

def generalPlanarOrbitSparseEncoding (hg : 1≤g) (a : ℕ)
    (o : GeneralPlanarOrbitAtCusps T (n:=n) (k:=k) hg a) :
    ((Fin r × Fin 2) → Fin (r+1)) × SparseCuspAssignment n r a :=
  ((generalPlanarOrbitPattern T hg o.val).1,
    ⟨(generalPlanarOrbitPattern T hg o.val).2,
      (generalPlanarOrbit_pattern_support_card T hg o.val).trans o.property⟩)

lemma generalPlanarOrbitSparseEncoding_injective (hg : 1≤g) (a : ℕ) :
    Function.Injective (generalPlanarOrbitSparseEncoding T (n:=n) (k:=k) hg a) := by
  intro o p hop
  apply Subtype.ext
  apply generalPlanarOrbitPattern_injective T hg
  apply Prod.ext
  · exact congrArg (fun x : ((Fin r × Fin 2) → Fin (r+1)) × SparseCuspAssignment n r a => x.1) hop
  · exact congrArg (fun x : ((Fin r × Fin 2) → Fin (r+1)) × SparseCuspAssignment n r a => x.2.val) hop

lemma generalPlanarOrbitAtCusps_card_le (hg : 1≤g) (a : ℕ) :
    Fintype.card (GeneralPlanarOrbitAtCusps T (n:=n) (k:=k) hg a)≤
      (r+1)^(2*r)*n^a*(r+1)^a := by
  classical
  calc
    _ ≤ Fintype.card (((Fin r × Fin 2) → Fin (r+1)) × SparseCuspAssignment n r a) :=
      Fintype.card_le_of_injective _ (generalPlanarOrbitSparseEncoding_injective T hg a)
    _ = (r+1)^(2*r)*Fintype.card (SparseCuspAssignment n r a) := by simp [Nat.mul_comm]
    _ ≤ (r+1)^(2*r)*(n^a*(r+1)^a) := Nat.mul_le_mul_left _ (sparseCuspAssignment_card_le n r a)
    _ = _ := by ring
end WP.RandomGeometry
