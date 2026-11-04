import WPFormalization.Analysis.JTCriticalAction

/-! Replacing the full action in the actual fixed-marking model.
The logarithmic factor is bounded by C_p*g*sqrt(x_c-x); the genus factor
is retained and no arbitrary joint-limit relative convergence is asserted. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace WP.Analysis

lemma jt_action_log_relative_bound :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ Y ∈ Ico (0:ℝ) y₀, y₀-Y ≤ ε →
        |Real.log (Z Y/jtCriticalAction Y)| ≤ C*Real.sqrt (xCritical-XR Y) := by
  obtain ⟨C,hC,hbound⟩ := jt_action_log_relative_gap.exists_pos
  have he := hbound.bound
  rw [eventually_nhdsWithin_iff] at he
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨C,ε/2,hC,by positivity,?_⟩
  intro Y hY hδ
  have hd : dist Y y₀ < ε := by
    rw [Real.dist_eq,abs_of_neg (sub_neg.mpr hY.2)]
    linarith
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using he hd hY.2

lemma jt_action_power_replacement (Y : ℝ) (hY : Y ∈ Ico (0:ℝ) y₀) (h : ℕ) :
    (Z Y)⁻¹^h = (jtCriticalAction Y)⁻¹^h *
      Real.exp ((h:ℝ)*Real.log (jtCriticalAction Y/Z Y)) := by
  have he := nat_power_log_factorization 1 (jtCriticalAction Y) (Z Y) 1 1 h
    (jtCriticalAction_pos Y hY) (marked_Z_pos Y hY) one_ne_zero
  simpa only [one_mul,mul_one,div_one] using he

/-- The original model with precisely its action factor replaced by the
leading critical power. All other genus and marking factors are unchanged. -/
def jtCriticalMarkedModel (g p : ℕ) (Y : ℝ) : ℝ :=
  Real.Gamma (complexity g p) * (4:ℝ)⁻¹^g / Real.sqrt (Real.pi*complexity g p) *
    (jtCriticalAction Y)⁻¹^(complexity g p) *
    Real.rpow (r Y) ((p:ℝ)/2) * Real.sqrt (A Y*Theta Y)

lemma jt_marked_model_replacement_identity (g p : ℕ) (Y : ℝ)
    (hY : Y ∈ Ico (0:ℝ) y₀) :
    markedModel g p Y = jtCriticalMarkedModel g p Y *
      Real.exp ((complexity g p:ℝ)*Real.log (jtCriticalAction Y/Z Y)) := by
  unfold markedModel jtCriticalMarkedModel
  rw [jt_action_power_replacement Y hY (complexity g p)]
  ring

lemma jt_marked_critical_replacement (p : ℕ) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ g : ℕ, 1 ≤ g → ∀ Y ∈ Ico (0:ℝ) y₀, y₀-Y ≤ ε →
        ∃ e : ℝ, |e| ≤ C*(g:ℝ)*Real.sqrt (xCritical-XR Y) ∧
          markedModel g p Y = jtCriticalMarkedModel g p Y*Real.exp e := by
  obtain ⟨C,ε,hC,hε,hlog⟩ := jt_action_log_relative_bound
  refine ⟨((p:ℝ)+2)*C,ε,by positivity,hε,?_⟩
  intro g hg Y hY hsmall
  let e : ℝ := (complexity g p:ℝ)*Real.log (jtCriticalAction Y/Z Y)
  refine ⟨e,?_,jt_marked_model_replacement_identity g p Y hY⟩
  have hZ := marked_Z_pos Y hY
  have hL := jtCriticalAction_pos Y hY
  have hinv : Real.log (jtCriticalAction Y/Z Y) = -Real.log (Z Y/jtCriticalAction Y) := by
    rw [Real.log_div hL.ne' hZ.ne',Real.log_div hZ.ne' hL.ne']
    ring
  have hcomp : (complexity g p:ℝ) ≤ ((p:ℝ)+2)*(g:ℝ) := by
    have hn : complexity g p ≤ (p+2)*g := by
      unfold complexity
      have hp : p ≤ p*g := by simpa only [mul_one] using Nat.mul_le_mul_left p hg
      calc
        2*g+p-2 ≤ 2*g+p := Nat.sub_le _ _
        _ ≤ 2*g+p*g := Nat.add_le_add_left hp _
        _ = (p+2)*g := by ring
    exact_mod_cast hn
  dsimp only [e]
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _),hinv,abs_neg]
  calc
    _ ≤ (complexity g p:ℝ)*(C*Real.sqrt (xCritical-XR Y)) :=
      mul_le_mul_of_nonneg_left (hlog Y hY hsmall) (Nat.cast_nonneg _)
    _ ≤ (((p:ℝ)+2)*(g:ℝ))*(C*Real.sqrt (xCritical-XR Y)) :=
      mul_le_mul_of_nonneg_right hcomp (mul_nonneg hC.le (Real.sqrt_nonneg _))
    _ = _ := by ring

@[blueprint "eq:jt-critical-action"]
theorem jt_critical_action :
    ((fun Y => (xCritical-XR Y)/((criticalB/2)*(y₀-Y)^2)-1)
      =O[𝓝[<] y₀] (fun Y => y₀-Y)) ∧
    ((fun Y => Z Y/((2*Real.sqrt 3*criticalB/5)*Real.rpow (y₀-Y) (5/2:ℝ))-1)
      =O[𝓝[<] y₀] (fun Y => y₀-Y)) ∧
    ((fun Y => Z Y/((Real.rpow 2 (9/4:ℝ)*Real.sqrt 3/
        (5*Real.rpow criticalB (1/4:ℝ)))*Real.rpow (xCritical-XR Y) (5/4:ℝ))-1)
      =O[𝓝[<] y₀] (fun Y => Real.sqrt (xCritical-XR Y))) ∧
    (∀ p : ℕ, 1 ≤ p → ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ g : ℕ, 1 ≤ g → ∀ Y ∈ Ico (0:ℝ) y₀, y₀-Y ≤ ε →
        ∃ e : ℝ, |e| ≤ C*(g:ℝ)*Real.sqrt (xCritical-XR Y) ∧
          markedModel g p Y = jtCriticalMarkedModel g p Y*Real.exp e) := by
  exact ⟨jt_gap_relative_delta,jt_action_relative_delta,jt_action_relative_gap,
    fun p _ => jt_marked_critical_replacement p⟩

end WP.Analysis
