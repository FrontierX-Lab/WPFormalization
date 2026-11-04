import WPFormalization.Critical.SurvivingMixedCurveTypes
import WPFormalization.RandomGeometry.CurveLengthPointMeasures
import WPFormalization.RandomGeometry.PantsOrbitLabels
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry MeasureTheory
open scoped Classical ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    {g n : ℕ}

abbrev NonseparatingOrbit (g n : ℕ) := {o : T.Orbit g n 1 // (T.cut o).components=1}
instance : Fintype (NonseparatingOrbit T g n) := inferInstanceAs (Fintype (Subtype _))

abbrev NonseparatingIndex (X : G.Moduli g n (fun _ => 0)) :=
  Σ o : NonseparatingOrbit T g n,
    {γ : Fin 1 → H.Primitive g n X // T.orbitMem o.val X γ}

def nonseparatingIndexToCurve (X : G.Moduli g n (fun _ => 0)) :
    NonseparatingIndex T X → {γ : H.Primitive g n X // IsNonseparating T γ} := fun j =>
  ⟨j.2.val 0,j.1.val,by
    have he : (fun _ : Fin 1 => j.2.val 0)=j.2.val := by funext i;rw [Fin.eq_zero i]
    rw [he]
    exact j.2.property,j.1.property⟩

lemma nonseparatingIndexToCurve_injective (X : G.Moduli g n (fun _ => 0)) :
    Function.Injective (nonseparatingIndexToCurve T X) := by
  rintro ⟨o,γ⟩ ⟨p,δ⟩ he
  have hv : γ.val=δ.val := by
    have h0 : γ.val 0=δ.val 0 := congrArg Subtype.val he
    funext i
    rw [Fin.eq_zero i]
    exact h0
  have hop : o=p := Subtype.ext (orbitMem_unique T o.val p.val X γ.val γ.property
    (hv ▸ δ.property))
  subst p
  congr 1
  exact Subtype.ext hv

lemma nonseparatingIndexToCurve_surjective (X : G.Moduli g n (fun _ => 0)) :
    Function.Surjective (nonseparatingIndexToCurve T X) := by
  rintro ⟨γ,o,ho,hc⟩
  exact ⟨⟨⟨o,hc⟩,⟨fun _ => γ,ho⟩⟩,Subtype.ext rfl⟩

def nonseparatingIndexEquiv (X : G.Moduli g n (fun _ => 0)) :
    NonseparatingIndex T X ≃ {γ : H.Primitive g n X // IsNonseparating T γ} :=
  Equiv.ofBijective (nonseparatingIndexToCurve T X)
    ⟨nonseparatingIndexToCurve_injective T X,nonseparatingIndexToCurve_surjective T X⟩

/-- The genuine physical nonseparating length point measure, with scale one. -/
def nonseparatingLengthPointMeasure (X : G.Moduli g n (fun _ => 0)) :
    WP.Probability.PointMeasure ℝ≥0 :=
  curveLengthPointMeasure H X 1 (by norm_num) (IsNonseparating T)

def nonseparatingWindowTest (B : Set ℝ≥0) (x : Fin 1 → ℝ) : ℝ≥0∞ :=
  if Real.toNNReal (x 0) ∈ B then 1 else 0

lemma nonseparatingWindowTest_measurable (B : Set ℝ≥0) (hB : MeasurableSet B) :
    Measurable (nonseparatingWindowTest B) := by
  have hm : Measurable (fun x : Fin 1 → ℝ => Real.toNNReal (x 0)) :=
    continuous_real_toNNReal.measurable.comp (measurable_pi_apply 0)
  exact measurable_const.ite (hB.preimage hm) measurable_const

lemma nonseparatingLengthPointMeasure_eq_orbitSum (X : G.Moduli g n (fun _ => 0))
    (B : Set ℝ≥0) (hB : MeasurableSet B) :
    (nonseparatingLengthPointMeasure T X).toMeasure B=
      ∑ o : NonseparatingOrbit T g n,T.orbitSum o.val (nonseparatingWindowTest B) X := by
  change (curveNNLengthMeasure H X 1 (IsNonseparating T)) B=_
  rw [curveNNLengthMeasure,Measure.sum_apply _ hB]
  simp only [one_mul,Measure.dirac_apply' _ hB]
  calc
    _ = ∑' j : NonseparatingIndex T X,
        B.indicator (fun _ => (1 : ℝ≥0∞)) (Real.toNNReal (H.length (j.2.val 0))) := by
      exact ((nonseparatingIndexEquiv T X).tsum_eq
        (fun γ => B.indicator (fun _ => (1 : ℝ≥0∞)) (Real.toNNReal (H.length γ.val)))).symm
    _ = _ := by
      rw [ENNReal.tsum_sigma',tsum_fintype]
      apply Finset.sum_congr rfl
      intro o ho
      apply tsum_congr
      intro γ
      rfl

include T in
lemma nonseparatingLengthPointMeasure_measurable_window (MI : MirzakhaniIntegration G H T)
    (B : Set ℝ≥0) (hB : MeasurableSet B) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      (nonseparatingLengthPointMeasure T X).toMeasure B) := by
  simp_rw [nonseparatingLengthPointMeasure_eq_orbitSum T _ B hB]
  apply Finset.measurable_sum
  intro o ho
  exact MI.orbitSum_measurable _ _ (nonseparatingWindowTest_measurable B hB)
include T in
lemma nonseparatingLengthPointMeasure_measurable_count (MI : MirzakhaniIntegration G H T)
    (B : WP.Probability.RelCompactBorelWindow ℝ≥0) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      (nonseparatingLengthPointMeasure T X).count ℝ≥0 B) := by
  apply measurable_to_countable'
  intro a
  have hm := nonseparatingLengthPointMeasure_measurable_window T (g:=g) (n:=n) MI B.carrier B.measurableSet
  convert hm (measurableSet_singleton (a : ℝ≥0∞)) using 1
  ext X
  simp only [Set.mem_preimage,Set.mem_singleton_iff]
  rw [(nonseparatingLengthPointMeasure T X).count_spec ℝ≥0 B]
  exact Nat.cast_inj.symm
end WP.Critical
