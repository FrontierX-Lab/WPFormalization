import WPFormalization.RandomGeometry.GeneralPlanarOrbitPatterns
import WPFormalization.RandomGeometry.GeneralPlanarRemainderIntegration
import WPFormalization.RandomGeometry.PlanarCutTreeBoundaryBudget
import WPFormalization.RandomGeometry.GeneralPlanarCutIntegralBound

/-! Actual nonstar orbits grouped by their occupied cusp labels and root
degree. These are functions of the genuine cut graph, not free parameters. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    {g n r : ℕ} {k : Fin r→ℕ}

def generalPlanarOrbitCusps (hg : 1≤g) (o : GeneralPlanarOrbit T g n r k) : ℕ :=
  PlanarCut.planarCuspCount (T.cut o.val) (generalPlanarOrbitRoot T hg o)

def generalPlanarOrbitDegree (hg : 1≤g) (o : GeneralPlanarOrbit T g n r k) : ℕ :=
  PlanarCut.rootDegree (T.cut o.val) (generalPlanarOrbitRoot T hg o)

lemma generalPlanarOrbit_cusps_upper (hg : 1≤g) (o : GeneralPlanarOrbit T g n r k) :
    generalPlanarOrbitCusps T hg o≤∑i,k i := by
  classical
  choose S hp hcard using o.property
  choose side hside hgenus hlabels using hp
  have hpos : 0<(T.cut o.val).genus (generalPlanarOrbitRoot T hg o) := by
    have hh := (generalPlanarOrbitRoot_spec T hg o).1
    omega
  exact PlanarCut.planarCuspCount_upper (T.cut o.val) (T.cut_connected o.val)
    side hside hgenus (generalPlanarOrbitRoot T hg o) hpos k (fun e=>by
    rw [hlabels e]
    exact hcard e)

lemma generalPlanarOrbit_cusps_lower (hg : 1≤g) (o : GeneralPlanarOrbit T g n r k) :
    r+generalPlanarOrbitDegree T hg o≤generalPlanarOrbitCusps T hg o :=
  PlanarCut.planarCuspCount_lower (T.cut o.val) (T.cut_connected o.val)
    (generalPlanarOrbit_sides T o) (generalPlanarOrbitRoot T hg o)
    (generalPlanarOrbitRoot_spec T hg o).2 (T.cut_stable o.val)

lemma generalPlanarRemainder_degree_lt (hg : 1≤g) (o : GeneralPlanarRemainderOrbit T g n r k) :
    generalPlanarOrbitDegree T hg o.val<r := by
  apply PlanarCut.nonstar_rootDegree_lt (T.cut o.val.val) hg k
    (T.cut_connected o.val.val) (T.cut_euler o.val.val) o.val.property
    (generalPlanarOrbitRoot T hg o.val) (generalPlanarOrbitRoot_spec T hg o.val).1
    (generalPlanarOrbitRoot_spec T hg o.val).2
  rintro ⟨f,hf⟩
  apply o.property
  exact ⟨⟨o.val.val,f,hf⟩,Subtype.ext rfl⟩

def GeneralPlanarRemainderAtBudget (hg : 1≤g) (a d : ℕ) :=
  {o : GeneralPlanarRemainderOrbit T g n r k //
    generalPlanarOrbitCusps T hg o.val=a ∧ generalPlanarOrbitDegree T hg o.val=d}

instance (hg : 1≤g) (a d : ℕ) :
    Fintype (GeneralPlanarRemainderAtBudget T (n:=n) (k:=k) hg a d) := by
  classical
  unfold GeneralPlanarRemainderAtBudget
  infer_instance

lemma generalPlanarRemainderAtBudget_card_le (hg : 1≤g) (a d : ℕ) :
    Fintype.card (GeneralPlanarRemainderAtBudget T (n:=n) (k:=k) hg a d)≤
      (r+1)^(2*r)*n^a*(r+1)^a := by
  let f : GeneralPlanarRemainderAtBudget T (n:=n) (k:=k) hg a d→
      GeneralPlanarOrbitAtCusps T (n:=n) (k:=k) hg a := fun o=>⟨o.val.val,o.property.1⟩
  have hi : Function.Injective f := by
    intro o p hop
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : GeneralPlanarOrbitAtCusps T (n:=n) (k:=k) hg a=>q.val) hop
  exact (Fintype.card_le_of_injective f hi).trans (generalPlanarOrbitAtCusps_card_le T hg a)

lemma generalPlanarRemainderAtBudget_nonempty_bounds (hg : 1≤g) (a d : ℕ)
    (ho : Nonempty (GeneralPlanarRemainderAtBudget T (n:=n) (k:=k) hg a d)) :
    a≤∑i,k i ∧ r+d≤a ∧ d<r := by
  obtain ⟨o⟩ := ho
  have h1 := generalPlanarOrbit_cusps_upper T hg o.val.val
  have h2 := generalPlanarOrbit_cusps_lower T hg o.val.val
  have h3 := generalPlanarRemainder_degree_lt T hg o.val
  rw [o.property.1] at h1 h2
  rw [o.property.2] at h2 h3
  exact ⟨h1,h2,h3⟩

def generalPlanarCutWindowIntegral (D : MulticurveCutData n r)
    (I : Fin r→Set ℝ) : ℝ≥0∞ :=
  ∫⁻x : Fin r→ℝ in {x | ∀i,0≤x i},
    pantsWindowTest I x*ENNReal.ofReal (D.volumeProduct G x)*∏i,ENNReal.ofReal (x i)

include G in
lemma generalPlanarRemainder_cut_integral_upper (hg : 1≤g)
    (hn : (∑i,k i)<n) (o : GeneralPlanarRemainderOrbit T g n r k)
    (I : Fin r→Set ℝ) (L : ℝ) (hL : 0≤L) (hsub : ∀i,I i⊆Icc 0 L) :
    generalPlanarCutWindowIntegral (G:=G) (T.cut o.val.val) I≤
      ENNReal.ofReal (Real.exp ((r:ℝ)*L)*
        volumeModel P g (n-generalPlanarOrbitCusps T hg o.val+generalPlanarOrbitDegree T hg o.val)*
        (generalPlanarZeroVolumeCap P ((∑i,k i)+2*r))^r*(L^2/2)^r) := by
  let D := T.cut o.val.val
  let root := generalPlanarOrbitRoot T hg o.val
  have hroot := generalPlanarOrbitRoot_spec T hg o.val
  have hcuts := generalPlanarOrbit_sides T o.val
  have ha := generalPlanarOrbit_cusps_upper T hg o.val
  have hrootcount := PlanarCut.root_boundaryCount D hcuts root
  have hm : 1≤D.boundaryCount root := by
    change D.boundaryCount root=n-generalPlanarOrbitCusps T hg o.val+generalPlanarOrbitDegree T hg o.val
      at hrootcount
    omega
  have hu := generalPlanar_cut_window_integral_upper P G D g ((∑i,k i)+2*r) hg
    (PlanarCut.components_eq_edges_add_one D (T.cut_connected o.val.val) hcuts) root
    hroot.1 hroot.2 (T.cut_stable o.val.val) hm
    (fun c hc=>PlanarCut.nonroot_boundaryCount_le_sum D root c hc k ha) I L hL hsub
  change D.boundaryCount root=n-generalPlanarOrbitCusps T hg o.val+generalPlanarOrbitDegree T hg o.val
    at hrootcount
  simpa only [hrootcount,generalPlanarCutWindowIntegral] using hu

end WP.RandomGeometry
