import WPFormalization.JT.BesselEnergy
import WPFormalization.Volumes.StringFlowProof
import WPFormalization.Geometry.Bridge

/-! The exact JT cusp-weight dictionary of Section 15.1.
The Bessel string expression uses the entire energy series, including E < 0.
The generating-function theorem concerns actual geometric cusp volumes under
the existing explicit classical WP realization, and includes convergence.
No string equation or normalization identity is introduced as a new axiom. -/
noncomputable section
universe u v
namespace WP.JT
open Set
open WP.External

lemma stringBesselEnergy_edge (Y : ℝ) :
    stringBesselEnergy (edgeEnergy Y) = -XR Y/(2*Real.pi^2) := by
  rw [stringBesselEnergy_eq_XR, edgeEnergy]
  congr 2
  field_simp [Real.pi_ne_zero]

/-- Substituting E₀=-Y/π² into the entire string equation gives X(Y)=x,
with x=2π²λ_def. This is valid also at negative E₀. -/
theorem string_equation_iff (Y lambdaDef : ℝ) :
    stringBesselEnergy (edgeEnergy Y)+lambdaDef=0 ↔ XR Y=2*Real.pi^2*lambdaDef := by
  rw [stringBesselEnergy_edge]
  have hc : 0 < 2*Real.pi^2 := by positivity
  constructor
  · intro h
    have he : -XR Y/(2*Real.pi^2) = -lambdaDef := by linarith
    have hm := (div_eq_iff hc.ne').mp he
    linarith
  · intro h
    rw [h]
    field_simp
    ring

lemma string_equation_zero : stringBesselEnergy (edgeEnergy 0)=0 := by
  rw [stringBesselEnergy_edge]
  simp [XR, X]

/-- The branch attached to the undeformed edge is the already constructed
inverse branch of X. Uniqueness is on the physical interval [0,y₀). -/
theorem string_equation_branch (lambdaDef : ℝ) (hWeight : 0 ≤ lambdaDef)
    (hx : 2*Real.pi^2*lambdaDef < xCritical) :
    inverseY (2*Real.pi^2*lambdaDef) ∈ Ico 0 y₀ ∧
    stringBesselEnergy (edgeEnergy (inverseY (2*Real.pi^2*lambdaDef)))+lambdaDef=0 ∧
    ∀ Y ∈ Ico 0 y₀, stringBesselEnergy (edgeEnergy Y)+lambdaDef=0 →
      Y=inverseY (2*Real.pi^2*lambdaDef) := by
  have hb := inverseY_branch (2*Real.pi^2*lambdaDef) ⟨by positivity, hx⟩
  refine ⟨hb.1, (string_equation_iff _ _).2 hb.2, ?_⟩
  intro Y hY he
  exact (Analysis.inverseY_eq_of_root _ Y hY.2.le ((string_equation_iff _ _).1 he)).symm

lemma edgeEnergy_inverse_zero : edgeEnergy (inverseY 0)=0 := by
  rw [Analysis.inverseY_zero_value]
  simp [edgeEnergy]

/-- The same physical branch includes its critical endpoint. This is a statement
about the string equation, and does not assert convergence of Phi at x_c. -/
theorem string_equation_branch_closed (lambdaDef : ℝ) (hWeight : 0 ≤ lambdaDef)
    (hx : 2*Real.pi^2*lambdaDef ≤ xCritical) :
    inverseY (2*Real.pi^2*lambdaDef) ∈ Icc 0 y₀ ∧
    stringBesselEnergy (edgeEnergy (inverseY (2*Real.pi^2*lambdaDef)))+lambdaDef=0 ∧
    ∀ Y ∈ Icc 0 y₀, stringBesselEnergy (edgeEnergy Y)+lambdaDef=0 →
      Y=inverseY (2*Real.pi^2*lambdaDef) := by
  have hroot : XR (inverseY (2*Real.pi^2*lambdaDef))=2*Real.pi^2*lambdaDef := by
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact (inverseY_branch _ ⟨by positivity, hlt⟩).2
    · have hi : inverseY xCritical=y₀ :=
        Analysis.inverseY_eq_of_root xCritical y₀ le_rfl rfl
      rw [heq, hi]
      rfl
  have hmem : inverseY (2*Real.pi^2*lambdaDef) ∈ Icc 0 y₀ := by
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact Ico_subset_Icc_self (inverseY_branch _ ⟨by positivity, hlt⟩).1
    · rw [heq, Analysis.inverseY_eq_of_root xCritical y₀ le_rfl rfl]
      exact ⟨y₀_pos.le, le_rfl⟩
  refine ⟨hmem, (string_equation_iff _ _).2 hroot, ?_⟩
  intro Y hY he
  exact (Analysis.inverseY_eq_of_root _ Y hY.2 ((string_equation_iff _ _).1 he)).symm

/-- The exact coefficient scaling, before taking any infinite sum. -/
lemma defect_coefficient_scaling (P : PsiTheory) (g n : ℕ) (hg : 2 ≤ g)
    (lambdaDef : ℂ) :
    (volumeModel P g n : ℂ)*lambdaDef^n/(n.factorial : ℂ) =
      (2*(Real.pi : ℂ)^2)^(3*g-3) *
        ((shifted P g (List.replicate n 0) 0 : ℂ)/(n.factorial : ℂ)*
          (2*(Real.pi : ℂ)^2*lambdaDef)^n) := by
  have hd : dimension g n = 3*g-3+n := by unfold dimension; omega
  unfold volumeModel mixedBracket
  simp only [List.sum_replicate, smul_zero, pow_zero, one_mul,
    deficit, List.length_replicate, Nat.sub_zero, hd]
  push_cast
  rw [pow_add, mul_pow]
  ring

/-- On the full established convergence disk, the defect-weighted amplitude
has the stated factor (2π²)^(3g−3), including the n=0 coefficient. -/
theorem model_defect_amplitude_hasSum (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g)
    (lambdaDef : ℂ) (hWeight : ‖2*(Real.pi : ℂ)^2*lambdaDef‖ < xCritical) :
    HasSum (fun n : ℕ => (volumeModel P g n : ℂ)*lambdaDef^n/(n.factorial : ℂ))
      ((2*(Real.pi : ℂ)^2)^(3*g-3)*Phi P g (2*(Real.pi : ℂ)^2*lambdaDef)) := by
  have hs := (Phi_hasSum_shifted P g _ hWeight).mul_left ((2*(Real.pi : ℂ)^2)^(3*g-3))
  exact hs.congr_fun (fun n => defect_coefficient_scaling P g n hg lambdaDef)

/-- The corresponding identity for actual geometric cusp volumes. All geometric
assumptions are the pre-existing classical realization; no new input is added. -/
theorem geometric_defect_amplitude_hasSum (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (g : ℕ) (hg : 2 ≤ g)
    (lambdaDef : ℂ) (hWeight : ‖2*(Real.pi : ℂ)^2*lambdaDef‖ < xCritical) :
    HasSum (fun n : ℕ => (cuspVolume G g n : ℂ)*lambdaDef^n/(n.factorial : ℂ))
      ((2*(Real.pi : ℂ)^2)^(3*g-3)*Phi P g (2*(Real.pi : ℂ)^2*lambdaDef)) := by
  apply (model_defect_amplitude_hasSum P g hg lambdaDef hWeight).congr_fun
  intro n
  rw [Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable; omega)]

theorem geometric_defect_amplitude (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (g : ℕ) (hg : 2 ≤ g)
    (lambdaDef : ℝ) (hWeight : |2*Real.pi^2*lambdaDef| < xCritical) :
    HasSum (fun n : ℕ => cuspVolume G g n*lambdaDef^n/(n.factorial : ℝ))
      ((2*Real.pi^2)^(3*g-3)*(Phi P g (2*Real.pi^2*lambdaDef)).re) := by
  have hc : ‖2*(Real.pi : ℂ)^2*(lambdaDef : ℂ)‖ < xCritical := by
    have he : 2*(Real.pi : ℂ)^2*(lambdaDef : ℂ) = ((2*Real.pi^2*lambdaDef : ℝ) : ℂ) := by
      push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    exact hWeight
  have hs := Complex.hasSum_re (geometric_defect_amplitude_hasSum P G g hg lambdaDef hc)
  convert hs using 1
  · ext n
    norm_cast
  · have he : 2*(Real.pi : ℂ)^2 = ((2*Real.pi^2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he]
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]

theorem geometric_defect_amplitude_eq (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (g : ℕ) (hg : 2 ≤ g)
    (lambdaDef : ℝ) (hWeight : |2*Real.pi^2*lambdaDef| < xCritical) :
    (∑' n : ℕ, cuspVolume G g n*lambdaDef^n/(n.factorial : ℝ)) =
      (2*Real.pi^2)^(3*g-3)*(Phi P g (2*Real.pi^2*lambdaDef)).re :=
  (geometric_defect_amplitude P G g hg lambdaDef hWeight).tsum_eq

end WP.JT
