import WPFormalization.Analysis.JointNormalizedMorseModelDomain
import WPFormalization.Volumes.CompactMorseDomain
/-! The given actual compact phase and amplitude data produce a genuine common Morse domain together with JOINT holomorphy of every transformed amplitude on its shared parameter/coordinate product. The original fiber-domain API and canonical family remain unchanged. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma exists_joint_compact_morse_model_domain_at (P : PsiTheory) (p : ℕ)
    (S l Bc : ℂ → ℂ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) xCritical)
    (hS : AnalyticAt ℂ S (x : ℂ)) (hl : AnalyticAt ℂ l (x : ℂ))
    (hBc : AnalyticAt ℂ Bc (x : ℂ)) (hBcr : Bc (x : ℂ) = (extractionB p x : ℂ))
    (hnorm : ∀ᶠ q : ℂ in 𝓝 (x : ℂ), (l q)^2 * ((complexEuler^[2]) S) q = 1)
    (Ω : Set ℂ) (f : ℕ → ℂ → ℂ) (C B : ℝ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y ∈ Icc (0 : ℝ) y₀, (Y : ℂ) ∈ Ω)
    (hC : 0 < C) (hB : 0 < B) (hf : ∀ j, AnalyticOnNhd ℂ (f j) Ω)
    (hbound : ∀ j z, z ∈ Ω → ‖f j z‖ ≤ C * B^j * (j.factorial : ℝ)^2) :
    ∃ d : NormalizedMorseModelDomain (compactMorsePhase S l x)
      (compactMorseBase Bc l x) (compactMorseParameter P l x) f B,
      ∀ j, AnalyticOnNhd ℂ (morseTransformedAmplitude
        (compactMorseBase Bc l x) (compactMorseParameter P l x) f d.U j)
        (Metric.ball (0 : ℂ) d.rho ×ˢ Metric.ball (0 : ℂ) d.R) := by
  let T : ℂ × ℂ → ℂ × ℂ := fun z => ((x : ℂ) + z.1, z.2)
  have hT : AnalyticAt ℂ T (0, 0) :=
    (analyticAt_const.add analyticAt_fst).prod analyticAt_snd
  have hT0 : T (0, 0) = ((x : ℂ), 0) := by simp [T]
  have harg : AnalyticAt ℂ (fun z : ℂ × ℂ => compactModelPoint l (T z)) (0, 0) :=
    (compactModelPoint_analyticAt l (x : ℂ) hl).comp_of_eq hT hT0
  have harg0 : compactModelPoint l (T (0, 0)) = (x : ℂ) := by
    rw [hT0, compactModelPoint_axis]
  have hn : Bc (x : ℂ) ≠ 0 := by
    rw [hBcr]
    exact_mod_cast (extractionB_pos_interior p x ⟨hx.1.le, hx.2⟩).ne'
  have hbase : AnalyticAt ℂ (compactMorseBase Bc l x) (0, 0) :=
    (hBc.comp_of_eq harg harg0).div
      (hBc.comp_of_eq (analyticAt_const.add analyticAt_fst) (by simp)) (by simpa using hn)
  have hxN : ‖(x : ℂ)‖ < xCritical := by
    rw [Complex.norm_of_nonneg hx.1.le]
    exact hx.2
  have hpar : AnalyticAt ℂ (compactMorseParameter P l x) (0, 0) :=
    (PositiveConvolution.planarInverse_analyticAt P (x : ℂ) hxN).comp_of_eq harg harg0
  have hpar0 : compactMorseParameter P l x (0, 0) ∈ Ω := by
    change PositiveConvolution.planarInverse P (compactModelPoint l (T (0, 0))) ∈ Ω
    rw [harg0, PositiveConvolution.planarInverse_ofReal P x ⟨hx.1.le, hx.2⟩]
    have hY := (inverseY_branch x ⟨hx.1.le, hx.2⟩).1
    exact hcover _ ⟨hY.1, hY.2.le⟩
  exact exists_joint_normalized_morse_model_domain (compactMorsePhase S l x)
    (compactMorseBase Bc l x) (compactMorseParameter P l x)
    (centeredExponentialPhase_shifted_analyticAt S l x hS hl) hbase hpar
    (centeredExponentialPhase_shifted_normalized_jets S l x hS hnorm)
    Ω f C B hΩ hpar0 hC hB hf hbound

end WP.Analysis
