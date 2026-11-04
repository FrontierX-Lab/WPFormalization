import WPFormalization.RandomGeometry.GeneralPlanarMomentDecomposition
import WPFormalization.RandomGeometry.PlanarCutTreeStar

/-! The actual one-planar-curve moment: every one-edge planar cut is a star.
The formula includes every cusp type through k=n, without a side-exchange factor. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T) {g n : ℕ}

lemma generalPlanar_single_star_surjective (hg : 1≤g) (k : Fin 1 → ℕ) :
    Function.Surjective (generalPlanarStarOrbitEmbedding T g n 1 k) := by
  intro o
  obtain ⟨f,hf⟩ := PlanarCut.one_edge_exists_generalPlanarStar_iso (T.cut o.val) hg rfl k
    (T.cut_connected o.val) (T.cut_euler o.val) o.property
  exact ⟨⟨o.val,f,hf⟩,Subtype.ext rfl⟩

lemma generalPlanar_single_remainder_isEmpty (hg : 1≤g) (k : Fin 1 → ℕ) :
    IsEmpty (GeneralPlanarRemainderOrbit T g n 1 k) := by
  constructor
  intro o
  exact o.property (generalPlanar_single_star_surjective H T hg k o.val)

lemma generalPlanar_single_remainder_zero (hg : 1≤g) (k : Fin 1 → ℕ)
    (F : (Fin 1 → ℝ) → ℝ≥0∞) (X : G.Moduli g n (fun _ => 0)) :
    generalPlanarRemainderWindowSum T g n 1 k F X=0 := by
  letI := generalPlanar_single_remainder_isEmpty H T (n:=n) hg k
  exact ENNReal.tsum_eq_zero.mpr (fun o => isEmptyElim o)

lemma generalPlanar_single_count_eq_planarCount (X : G.Moduli g n (fun _ => 0))
    (k : ℕ) (L : ℝ) :
    generalPlanarWindowCount H X (fun _ : Fin 1 => k) L (fun _ => Set.Icc 0 L)=H.planarCount X k L := by
  classical
  let A := {γ : OrderedGeneralPlanarTuple (H:=H) X (fun _ : Fin 1 => k) L //
    ∀i,H.length (γ.val i)∈Set.Icc 0 L}
  let e : A ≃ {γ //γ∈H.shortPlanar X k L} :=
    {toFun:=fun γ=>⟨γ.val.val 0,γ.val.property.2 0⟩
     invFun:=fun γ=>⟨⟨fun _=>γ.val,fun a b _=>Subsingleton.elim a b,fun _=>γ.property⟩,
       fun _=>⟨(H.length_pos γ.val).le,((H.mem_shortPlanar X k L _).1 γ.property).1⟩⟩
     left_inv:=by
       intro γ
       apply Subtype.ext
       apply Subtype.ext
       funext i
       exact congrArg γ.val.val (Subsingleton.elim 0 i)
     right_inv:=by intro γ;rfl}
  change Nat.card A=_
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe,←H.planarCount_eq_card]

include C MI in
lemma generalPlanar_single_curve_moment (hg : 2≤g) (k : ℕ) (hk : 2≤k) (hkn : k≤n)
    (L : ℝ) (hL : L<2*Real.arsinh 1) :
    (∫X : G.Moduli g n (fun _ => 0),(H.planarCount X k L:ℝ) ∂wpProbability G g n) =
      generalPlanarStarWindowCut P g n 1 (fun _=>k) (fun _=>Set.Icc 0 L) := by
  have h := generalPlanar_actual_moment_decomposition H T C MI (g:=g) (n:=n) hg (fun _ : Fin 1=>k)
    (fun _=>hk) (by intro h;have hh:=congrArg Prod.snd h;simp only at hh;omega) L hL
    (fun _=>Set.Icc 0 L) (fun _=>measurableSet_Icc) (fun _=>Set.Subset.rfl)
  simp_rw [generalPlanar_single_count_eq_planarCount H,
    generalPlanar_single_remainder_zero H T (g:=g) (n:=n) (by omega)] at h
  simpa using h
end WP.RandomGeometry
