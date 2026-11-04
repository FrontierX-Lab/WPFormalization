import WPFormalization.HigherOrder.ProfileJointRecipeStep
import WPFormalization.HigherOrder.FiniteDataStage
import WPFormalization.HigherOrder.CurrentGenusScalarRecipe
import WPFormalization.HigherOrder.JointBoundaryCusp
import WPFormalization.HigherOrder.FiniteDataTargetBridges
/-! The common actual finite-data induction in the fixed ring Index J bJ. Every old profile frame is genuinely coarsened, the proved actual next-profile step constructs the current joint certificate, true dilaton moments construct the current cusp scalar, and the actual finite KdV/unit-descent step constructs genus. Strong induction supplies all orders through J and both exact frozen C.3 finite-data specifications. The only deferred dependency is the previously licensed Rouche input in actual absolute kernel moments; no unproved paper goal is assumed. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open Set
open JointBoundary

def stageProfile {P : PsiTheory} {J k : ℕ} (h : FiniteDataStage P J k) :
    ∀ q : ℕ, (Fin (q + 1) → Option (Fin (boundaryCutoff k + 1))) →
      MvPolynomial (Fin (q + 1)) (DataPolynomial J) := Classical.choose h

def stageCusp {P : PsiTheory} {J k : ℕ} (h : FiniteDataStage P J k) : ℕ → DataPolynomial J :=
  Classical.choose (Classical.choose_spec h)

def stageGenus {P : PsiTheory} {J k : ℕ} (h : FiniteDataStage P J k) : ℕ → DataPolynomial J :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec h))

lemma stageProfile_degree {P : PsiTheory} {J k : ℕ} (h : FiniteDataStage P J k)
    (q : ℕ) (σ : Fin (q + 1) → Option (Fin (boundaryCutoff k + 1))) :
    (stageProfile h q σ).totalDegree ≤ 2 * k :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))).1 q σ

lemma stageProfile_eval {P : PsiTheory} {J k : ℕ} (h : FiniteDataStage P J k)
    (q : ℕ) (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) (d : Fin (q + 1) → ℕ) :
    profileCoefficient P Y (List.ofFn d) k =
      MvPolynomial.eval₂ (dataEval J Y).toRingHom (fun i => (d i : ℝ))
        (stageProfile h q (classify (q + 1) (boundaryCutoff k) d)) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))).2.1 q Y hY d

lemma stageCusp_eval {P : PsiTheory} {J k : ℕ} (h : FiniteDataStage P J k)
    (p : ℕ) (hp : 1 ≤ p) (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) :
    cuspCoefficient P Y p k = dataEval J Y (stageCusp h p) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))).2.2.1 p hp Y hY

lemma stageGenus_eval {P : PsiTheory} {J k : ℕ} (h : FiniteDataStage P J k)
    (p : ℕ) (hp : 1 ≤ p) (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) :
    genusCoefficient P Y p k = dataEval J Y (stageGenus h p) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))).2.2.2 p hp Y hY

def oldProfileFrame (P : PsiTheory) (J k : ℕ) (hprev : ∀ i < k + 1, FiniteDataStage P J i)
    (q i : ℕ) (σ : Fin (q + 1) → Option (Fin (boundaryCutoff k + 1))) :
    MvPolynomial (Fin (q + 1)) (DataPolynomial J) :=
  if hi : i < k + 1 then coarsenStratumPolynomial (boundaryCutoff i) (boundaryCutoff k)
    (stageProfile (hprev i hi) q) σ else 0

lemma oldProfileFrame_degree (P : PsiTheory) (J k : ℕ) (hprev : ∀ i < k + 1, FiniteDataStage P J i)
    (q i : ℕ) (hi : i < k + 1) (σ) : (oldProfileFrame P J k hprev q i σ).totalDegree ≤ 2 * k := by
  rw [oldProfileFrame, dite_eq_left hi]
  exact (coarsenStratumPolynomial_degree _ _ _ _ (stageProfile_degree (hprev i hi) q) σ).trans
    (Nat.mul_le_mul_left 2 (by omega))

lemma oldProfileFrame_eval (P : PsiTheory) (J k : ℕ) (hprev : ∀ i < k + 1, FiniteDataStage P J i)
    (q i : ℕ) (hi : i < k + 1) (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) (d : Fin (q + 1) → ℕ) :
    profileCoefficient P Y (List.ofFn d) i =
      MvPolynomial.eval₂ (dataEval J Y).toRingHom (fun l => (d l : ℝ))
        (oldProfileFrame P J k hprev q i (classify (q + 1) (boundaryCutoff k) d)) := by
  rw [oldProfileFrame, dite_eq_left hi,
    coarsenStratumPolynomial_eval _ _ (boundaryCutoff_mono (by omega))]
  exact stageProfile_eval (hprev i hi) q Y hY d

def oldCuspData (P : PsiTheory) (J k : ℕ) (hprev : ∀ i < k + 1, FiniteDataStage P J i)
    (p i : ℕ) : DataPolynomial J := if hi : i < k + 1 then stageCusp (hprev i hi) p else 0

def oldGenusData (P : PsiTheory) (J k : ℕ) (hprev : ∀ i < k + 1, FiniteDataStage P J i)
    (p i : ℕ) : DataPolynomial J := if hi : i < k + 1 then stageGenus (hprev i hi) p else 0

lemma oldCuspData_eval (P : PsiTheory) (J k : ℕ) (hprev : ∀ i < k + 1, FiniteDataStage P J i)
    (p : ℕ) (hp : 1 ≤ p) (i : ℕ) (hi : i < k + 1) (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) :
    cuspCoefficient P Y p i = dataEval J Y (oldCuspData P J k hprev p i) := by
  rw [oldCuspData, dite_eq_left hi]
  exact stageCusp_eval (hprev i hi) p hp Y hY

lemma oldGenusData_eval (P : PsiTheory) (J k : ℕ) (hprev : ∀ i < k + 1, FiniteDataStage P J i)
    (p : ℕ) (hp : 1 ≤ p) (i : ℕ) (hi : i < k + 1) (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) :
    genusCoefficient P Y p i = dataEval J Y (oldGenusData P J k hprev p i) := by
  rw [oldGenusData, dite_eq_left hi]
  exact stageGenus_eval (hprev i hi) p hp Y hY


lemma finiteDataStage_succ (P : PsiTheory) (J k : ℕ) (hJ : k + 1 ≤ J)
    (hprev : ∀ i < k + 1, FiniteDataStage P J i) : FiniteDataStage P J (k + 1) := by
  let F := oldProfileFrame P J k hprev
  let Cold := oldCuspData P J k hprev
  let Gold := oldGenusData P J k hprev
  have hcold : ∀ p ≥ 1, ∀ i < k + 1, ∀ Y ∈ Icc (0 : ℝ) y₀,
      cuspCoefficient P Y p i = (dataEval J Y).toRingHom (Cold p i) := by
    intro p hp i hi Y hY
    simpa only [Cold, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
      oldCuspData_eval P J k hprev p hp i hi Y hY
  have hgold : ∀ p ≥ 1, ∀ i < k + 1, ∀ Y ∈ Icc (0 : ℝ) y₀,
      genusCoefficient P Y p i = (dataEval J Y).toRingHom (Gold p i) := by
    intro p hp i hi Y hY
    simpa only [Gold, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
      oldGenusData_eval P J k hprev p hp i hi Y hY
  have hnext (m : ℕ) :
      ∃ Q : (Fin (m + 1) → Option (Fin (boundaryCutoff (k + 1) + 1))) →
          MvPolynomial (Fin (m + 1)) (DataPolynomial J),
        (∀ σ, (Q σ).totalDegree ≤ 2 * (k + 1)) ∧
        ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (m + 1) → ℕ,
          profileCoefficient P Y (List.ofFn d) (k + 1) =
            MvPolynomial.eval₂ (dataEval J Y).toRingHom (fun i => (d i : ℝ))
              (Q (classify (m + 1) (boundaryCutoff (k + 1)) d)) := by
    obtain ⟨Q, hdegree, hactual⟩ := actual_profile_joint_recipe_step P m k
      (boundaryCutoff k) (boundaryCutoff (k + 1)) (2 * k)
      (boundaryCutoff_handle k) (boundaryCutoff_separating k) F
      (fun q i hi σ => oldProfileFrame_degree P J k hprev q i hi σ)
      (fun Y => (dataEval J Y).toRingHom)
      (fun q i hi Y hY d => oldProfileFrame_eval P J k hprev q i hi Y hY d)
      (dataArea J) Cold Gold
      (by intro Y hY; simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using dataArea_eval J Y)
      hcold hgold (thetaDataMap J (k + 1) hJ) (fun Y hY => thetaDataMap_eval J (k + 1) hJ Y)
      (dataWeightMoment J) (dataWeightCoefficient J)
      (by
        intro Y hY j hj
        simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
          dataWeightMoment_hasSum J j (by omega) Y hY)
      (by
        intro Y hY l hl
        have hb : l ≤ boundaryCutoff J := (show l ≤ boundaryCutoff (k + 1) by omega).trans
          (boundaryCutoff_mono hJ)
        simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
          (dataWeightCoefficient_eval J l hb Y).symm)
    refine ⟨Q, ?_, hactual⟩
    intro σ
    exact (hdegree σ).trans_eq (by omega)
  let Fnew : ∀ q : ℕ, (Fin (q + 1) → Option (Fin (boundaryCutoff (k + 1) + 1))) →
      MvPolynomial (Fin (q + 1)) (DataPolynomial J) := fun q => Classical.choose (hnext q)
  have hdnew (q : ℕ) (σ) : (Fnew q σ).totalDegree ≤ 2 * (k + 1) :=
    (Classical.choose_spec (hnext q)).1 σ
  have henew (q : ℕ) (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) (d : Fin (q + 1) → ℕ) :
      profileCoefficient P Y (List.ofFn d) (k + 1) =
        MvPolynomial.eval₂ (dataEval J Y).toRingHom (fun i => (d i : ℝ))
          (Fnew q (classify (q + 1) (boundaryCutoff (k + 1)) d)) :=
    (Classical.choose_spec (hnext q)).2 Y hY d
  let Through : ∀ q : ℕ, ℕ → (Fin (q + 1) → Option (Fin (boundaryCutoff (k + 1) + 1))) →
      MvPolynomial (Fin (q + 1)) (DataPolynomial J) := fun q i σ =>
    if i = k + 1 then Fnew q σ else
      coarsenStratumPolynomial (boundaryCutoff k) (boundaryCutoff (k + 1)) (F q i) σ
  have hdthrough (q i : ℕ) (hi : i ≤ k + 1) (σ) : (Through q i σ).totalDegree ≤ 2 * (k + 1) := by
    by_cases he : i = k + 1
    · dsimp only [Through]
      rw [ite_eq_left he]
      exact hdnew q σ
    · dsimp only [Through]
      rw [ite_eq_right he]
      exact (coarsenStratumPolynomial_degree _ _ _ (F q i)
        (fun τ => oldProfileFrame_degree P J k hprev q i (by omega) τ) σ).trans (by omega)
  have hethrough (q i : ℕ) (hi : i ≤ k + 1) (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) (d : Fin (q + 1) → ℕ) :
      profileCoefficient P Y (List.ofFn d) i =
        MvPolynomial.eval₂ (dataEval J Y).toRingHom (fun l => (d l : ℝ))
          (Through q i (classify (q + 1) (boundaryCutoff (k + 1)) d)) := by
    by_cases he : i = k + 1
    · subst i
      dsimp only [Through]
      rw [ite_eq_left rfl]
      exact henew q Y hY d
    · dsimp only [Through]
      rw [ite_eq_right he,
        coarsenStratumPolynomial_eval _ _ (boundaryCutoff_mono (Nat.le_succ k))]
      exact oldProfileFrame_eval P J k hprev q i (by omega) Y hY d
  let Cnew : ℕ → DataPolynomial J := fun p =>
    cuspMomentRecipe p (k + 1) (boundaryCutoff (k + 1)) (2 * (k + 1)) (Through p)
      (dataDilatonMoment J) (dataDilatonCoefficient J) (dataInverseArea J)
  have hcnew (p : ℕ) (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) :
      cuspCoefficient P Y p (k + 1) = dataEval J Y (Cnew p) := by
    exact actual_cusp_moment_recipe P p (k + 1) (boundaryCutoff (k + 1)) (2 * (k + 1))
      (Through p) (fun i hi => hdthrough p i hi) (dataEval J) (fun i hi => hethrough p i hi)
      (dataDilatonMoment J) (dataDilatonCoefficient J) (dataInverseArea J)
      (by intro Z hZ j hj; exact dataDilatonMoment_hasSum J j (by omega) Z)
      (by
        intro Z hZ l hl
        have hb : l ≤ boundaryCutoff J := (show l ≤ boundaryCutoff (k + 1) by omega).trans
          (boundaryCutoff_mono hJ)
        exact (dataDilatonCoefficient_eval J l hb Z).symm)
      (fun Z hZ => dataInverseArea_eval J Z) Y hY
  let Cthrough : ℕ → ℕ → DataPolynomial J := fun p i =>
    if i = k + 1 then Cnew p else Cold p i
  have hcthrough : ∀ p ≥ 1, ∀ i ≤ k + 1, ∀ Y ∈ Icc (0 : ℝ) y₀,
      cuspCoefficient P Y p i = dataEval J Y (Cthrough p i) := by
    intro p hp i hi Y hY
    by_cases he : i = k + 1
    · subst i
      dsimp only [Cthrough]
      rw [ite_eq_left rfl]
      exact hcnew p Y hY
    · dsimp only [Cthrough]
      rw [ite_eq_right he]
      exact oldCuspData_eval P J k hprev p hp i (by omega) Y hY
  let E : List ℕ → DataPolynomial J := listRecipe (boundaryCutoff (k + 1)) Fnew
  have hE : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : List ℕ, 1 ≤ d.length →
      profileCoefficient P Y d (k + 1) = dataEval J Y (E d) := by
    intro Y hY d hd
    simpa only [E, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
      listRecipe_actual_eval P (k + 1) (boundaryCutoff (k + 1)) Fnew (dataEval J Y).toRingHom Y
        (fun q v => henew q Y hY v) d hd
  obtain ⟨Gnew, hgnew⟩ := current_genus_scalar_recipe_step P (k + 1) (by omega) (dataEval J) E hE
    (dataArea J) (fun Y hY => dataArea_eval J Y) Cthrough Gold hcthrough
    (fun p hp i hi Y hY => oldGenusData_eval P J k hprev p hp i hi Y hY)
    (thetaDataMap J (k + 1) hJ) (fun Y hY => thetaDataMap_eval J (k + 1) hJ Y)
  refine ⟨Fnew, Cnew, Gnew, hdnew, henew, ?_, hgnew⟩
  intro p hp Y hY
  exact hcnew p Y hY


theorem canonical_finite_data_stage (P : PsiTheory) (J k : ℕ) (hk : k ≤ J) :
    FiniteDataStage P J k := by
  revert hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    cases k with
    | zero => exact finiteDataStage_zero P J
    | succ k =>
      exact finiteDataStage_succ P J k hk (fun i hi => ih i hi (by omega))

theorem canonical_polynomial_dependence (P : PsiTheory) : PolynomialDependenceTarget P :=
  polynomialDependence_of_finiteDataStages P (canonical_finite_data_stage P)

theorem canonical_profile_boundary_polynomial (P : PsiTheory) : ProfileBoundaryPolynomialTarget P :=
  profileBoundaryPolynomial_of_finiteDataStages P (fun J => canonical_finite_data_stage P J J le_rfl)
end WP.HigherOrder.KernelFiniteData
