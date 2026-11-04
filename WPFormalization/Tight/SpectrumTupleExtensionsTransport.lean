import WPFormalization.External.TightGeodesicGeometry
/- Exact index/length-vector transport between the protected-empty cusp
presentation and the same actual G.Moduli/G.wpMeasure. These are proved identity
casts, including preservation of arbitrary scalar multiples and wpProbability;
no new geometric or probability premise is introduced. -/
noncomputable section
universe u v w z
namespace WP.External
open MeasureTheory
open scoped ENNReal

def indexMeasurableEquiv {I : Type z} (Ω : I → Type u)
    [∀ i, MeasurableSpace (Ω i)] {i j : I} (h : i = j) : Ω i ≃ᵐ Ω j := by
  cases h
  exact MeasurableEquiv.refl _

lemma indexMeasurableEquiv_measurePreserving {I : Type z} (Ω : I → Type u)
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i))
    {i j : I} (h : i = j) : MeasurePreserving (indexMeasurableEquiv Ω h) (μ i) (μ j) := by
  cases h
  exact ⟨measurable_id, Measure.map_id⟩

lemma indexMeasurableEquiv_apply_HEq {I : Type z} (Ω : I → Type u)
    [∀ i, MeasurableSpace (Ω i)] {i j : I} (h : i = j) (X : Ω i) :
    HEq (indexMeasurableEquiv Ω h X) X := by
  cases h
  rfl

lemma tightCuspIndex_eq (n : ℕ) :
    (⟨0+n, Fin.append (fun _ : Fin 0 => (0:ℝ)) (fun _ : Fin n => (0:ℝ))⟩ :
      Σ k : ℕ, Fin k → ℝ) = ⟨n, fun _ => 0⟩ := by
  simpa only [append_zero_lengths] using
    congrArg (fun k : ℕ => (⟨k, fun _ : Fin k => (0:ℝ)⟩ : Σ k : ℕ, Fin k → ℝ))
      (Nat.zero_add n)

def tightCuspMeasurableEquiv {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (g n : ℕ) : TightSurface G g 0 n (fun _ => 0) (fun _ => 0) ≃ᵐ
      G.Moduli g n (fun _ => 0) :=
  indexMeasurableEquiv (fun i : Σ k : ℕ, Fin k → ℝ => G.Moduli g i.1 i.2)
    (tightCuspIndex_eq n)

lemma tightCuspMeasurableEquiv_measurePreserving {P : PsiTheory}
    (G : WeilPeterssonGeometry.{u,v} P) (g n : ℕ) :
    MeasurePreserving (tightCuspMeasurableEquiv G g n)
      (G.wpMeasure g (0+n) (Fin.append (fun _ => 0) (fun _ => 0)))
      (G.wpMeasure g n (fun _ => 0)) :=
  indexMeasurableEquiv_measurePreserving
    (fun i : Σ k : ℕ, Fin k → ℝ => G.Moduli g i.1 i.2)
    (fun i => G.wpMeasure g i.1 i.2) (tightCuspIndex_eq n)

lemma tightCuspMeasurableEquiv_apply {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    {g n : ℕ} (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0)) :
    tightCuspMeasurableEquiv G g n X = tightCuspSurface G X := by
  have h₁ : HEq (tightCuspMeasurableEquiv G g n X) X := by
    exact indexMeasurableEquiv_apply_HEq
      (fun i : Σ k : ℕ, Fin k → ℝ => G.Moduli g i.1 i.2) (tightCuspIndex_eq n) X
  have h₂ : HEq (tightCuspSurface G X) X := by
    unfold tightCuspSurface
    simp only [eqRec_heq_iff]
    exact cast_heq _ _
  exact eq_of_heq (h₁.trans h₂.symm)



lemma tightCuspMeasurableEquiv_smul_measurePreserving {P : PsiTheory}
    (G : WeilPeterssonGeometry.{u,v} P) (g n : ℕ) (c : ℝ≥0∞) :
    MeasurePreserving (tightCuspMeasurableEquiv G g n)
      (c • G.wpMeasure g (0+n) (Fin.append (fun _ => 0) (fun _ => 0)))
      (c • G.wpMeasure g n (fun _ => 0)) := by
  refine ⟨(tightCuspMeasurableEquiv G g n).measurable, ?_⟩
  rw [Measure.map_smul, (tightCuspMeasurableEquiv_measurePreserving G g n).map_eq]
  exact (tightCuspMeasurableEquiv G g n).measurable.aemeasurable

lemma tightCuspMeasurableEquiv_wpProbability {P : PsiTheory}
    (G : WeilPeterssonGeometry.{u,v} P) (g n : ℕ) :
    MeasurePreserving (tightCuspMeasurableEquiv G g n)
      ((G.wpMeasure g n (fun _ => 0) Set.univ)⁻¹ •
        G.wpMeasure g (0+n) (Fin.append (fun _ => 0) (fun _ => 0)))
      (wpProbability G g n) :=
  tightCuspMeasurableEquiv_smul_measurePreserving G g n _

end WP.External
