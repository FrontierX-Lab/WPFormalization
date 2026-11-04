import WPFormalization.Analysis.NormalizedMorseModelDomain
import WPFormalization.Volumes.CompactPremorseModel
/-! At each physical compact-axis point, the given actual S/l/Bc and canonical coefficient family yield one joint normalized Morse domain. The given f/B are retained and the parameter radius precedes every amplitude order; this is a local neighborhood construction, not only a statement at the axis center. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

def compactMorsePhase (S l : ℂ → ℂ) (x : ℂ) (z : ℂ × ℂ) : ℂ :=
  centeredExponentialPhase S l (x + z.1, z.2)
def compactMorseBase (Bc l : ℂ → ℂ) (x : ℂ) (z : ℂ × ℂ) : ℂ :=
  Bc (compactModelPoint l (x + z.1, z.2)) / Bc (x + z.1)
def compactMorseParameter (P : PsiTheory) (l : ℂ → ℂ) (x : ℂ) (z : ℂ × ℂ) : ℂ :=
  PositiveConvolution.planarInverse P (compactModelPoint l (x + z.1, z.2))

lemma exists_compact_morse_model_domain_at (P : PsiTheory) (p : ℕ)
    (S l Bc : ℂ → ℂ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) xCritical)
    (hS : AnalyticAt ℂ S (x : ℂ)) (hl : AnalyticAt ℂ l (x : ℂ))
    (hBc : AnalyticAt ℂ Bc (x : ℂ)) (hBcr : Bc (x : ℂ) = (extractionB p x : ℂ))
    (hnorm : ∀ᶠ q : ℂ in 𝓝 (x : ℂ), (l q)^2 * ((complexEuler^[2]) S) q = 1)
    (Ω : Set ℂ) (f : ℕ → ℂ → ℂ) (C B : ℝ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y ∈ Icc (0 : ℝ) y₀, (Y : ℂ) ∈ Ω)
    (hC : 0 < C) (hB : 0 < B) (hf : ∀ j, AnalyticOnNhd ℂ (f j) Ω)
    (hbound : ∀ j z, z ∈ Ω → ‖f j z‖ ≤ C * B^j * (j.factorial : ℝ)^2) :
    Nonempty (NormalizedMorseModelDomain (compactMorsePhase S l x)
      (compactMorseBase Bc l x) (compactMorseParameter P l x) f B) := by
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
  exact exists_normalized_morse_model_domain (compactMorsePhase S l x)
    (compactMorseBase Bc l x) (compactMorseParameter P l x)
    (centeredExponentialPhase_shifted_analyticAt S l x hS hl) hbase hpar
    (centeredExponentialPhase_shifted_normalized_jets S l x hS hnorm)
    Ω f C B hΩ hpar0 hC hB hf hbound

lemma compactMorseSourceAmplitude_eq (P : PsiTheory) (Bc l : ℂ → ℂ)
    (f : ℕ → ℂ → ℂ) (x δ u : ℂ) (j : ℕ) :
    morseSourceAmplitude (compactMorseBase Bc l x) (compactMorseParameter P l x) f j (δ, u) =
      compactPremorseAmplitude P Bc l f j (x + δ, u) := rfl
end WP.Analysis
