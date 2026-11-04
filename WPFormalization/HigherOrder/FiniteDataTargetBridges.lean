import WPFormalization.HigherOrder.FiniteDataStage
import WPFormalization.Statements.FiniteKernelDataTarget
/-! Literal bridges from the common joint finite-data invariant to the two
fixed C.3 specifications. These helpers retain the common-stage premise;
the all-order stage producer must be supplied separately. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open Set JointBoundary

lemma polynomialDependence_of_finiteDataStages (P : PsiTheory)
    (hstage : ∀J k : ℕ,k ≤ J → FiniteDataStage P J k) : PolynomialDependenceTarget P := by
  classical
  intro p J hp
  choose F c g hdegree hprofile hc hg using hstage J
  let e : ℕ → List ℕ → DataPolynomial J := fun k d=>
    if hk : k ≤ J then listRecipe (boundaryCutoff k) (F k hk) d else 0
  let C : ℕ → DataPolynomial J := fun k=>if hk : k ≤ J then c k hk p else 0
  let G : ℕ → DataPolynomial J := fun k=>if hk : k ≤ J then g k hk p else 0
  refine ⟨boundaryCutoff J,e,C,G,?_⟩
  intro Y hY k hk
  refine ⟨?_,?_,?_⟩
  · intro d hd
    change profileCoefficient P Y d k=(dataEval J Y) (e k d)
    dsimp only [e]
    rw [dite_eq_left hk]
    exact listRecipe_actual_eval P k (boundaryCutoff k) (F k hk) (dataEval J Y).toRingHom Y
      (fun q v=>hprofile k hk q Y hY v) d (by omega)
  · change cuspCoefficient P Y p k=(dataEval J Y) (C k)
    dsimp only [C]
    rw [dite_eq_left hk]
    exact hc k hk p hp Y hY
  · change genusCoefficient P Y p k=(dataEval J Y) (G k)
    dsimp only [G]
    rw [dite_eq_left hk]
    exact hg k hk p hp Y hY

lemma finiteData_map_totalDegree_le {σ : Type*} {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (F : MvPolynomial σ R) : (MvPolynomial.map φ F).totalDegree ≤ F.totalDegree := by
  unfold MvPolynomial.totalDegree
  exact Finset.sup_mono (MvPolynomial.support_map_subset φ F)

lemma profileBoundaryPolynomial_of_finiteDataStages (P : PsiTheory)
    (hstage : ∀J : ℕ,FiniteDataStage P J J) : ProfileBoundaryPolynomialTarget P := by
  intro p J hp
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p≠0)
  obtain ⟨F,c,g,hdegree,hprofile,hc,hg⟩ := hstage J
  refine ⟨fun Y σ=>MvPolynomial.map (dataEval J Y).toRingHom (F q σ),?_,?_⟩
  · intro Y hY σ
    exact (finiteData_map_totalDegree_le _ _).trans (hdegree q σ)
  · intro Y hY d
    rw [MvPolynomial.eval_map]
    have hs : stratum (q+1) (boundaryCutoff J) d=classify (q+1) (boundaryCutoff J) d := rfl
    rw [hs]
    exact hprofile q Y hY d

end WP.HigherOrder.KernelFiniteData
