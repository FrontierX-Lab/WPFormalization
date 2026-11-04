import Mathlib
/-! Uniform normalization of a parameter family from its proved first-order remainder. -/
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology
lemma normalized_family_uniform (F : ℝ → ℂ → ℂ) (a r : ℝ → ℝ)
    (Y₀ : ℝ) (d : ℂ) (L : ℝ)
    (hAr : ∀ᶠ Y in 𝓝[<] Y₀, 0 < a Y ∧ 0 < r Y)
    (hrLim : Tendsto r (𝓝[<] Y₀) (𝓝 0))
    (hqLim : Tendsto (fun Y => r Y/a Y) (𝓝[<] Y₀) (𝓝 L))
    (hApprox : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ Y : ℝ, ∀ z : ℂ,
      |Y-Y₀| < δ → ‖z‖ < δ → ‖F Y z-(a Y : ℂ)-d*z‖ ≤ ε*‖z‖)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ Y in 𝓝[<] Y₀, ∀ w : ℂ, ‖w‖ ≤ R →
      ‖F Y ((r Y : ℂ)*w)/(a Y : ℂ)-(1+(d*(L : ℂ))*w)‖ ≤ ε := by
  let B : ℝ := |L|+1
  have hB : 0 < B := by dsimp [B]; positivity
  let e : ℝ := ε/(2*B*R)
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨δ,hδ,hbound⟩ := hApprox e he
  have hnormLim : Tendsto (fun Y => |r Y/a Y|) (𝓝[<] Y₀) (𝓝 |L|) := by
    simpa only [Real.norm_eq_abs] using hqLim.norm
  have hqB : ∀ᶠ Y in 𝓝[<] Y₀, |r Y/a Y| < B :=
    hnormLim.eventually (eventually_lt_nhds (by dsimp [B]; linarith : |L| < B))
  have hqc : Tendsto (fun Y => ((r Y/a Y : ℝ) : ℂ)) (𝓝[<] Y₀) (𝓝 (L : ℂ)) :=
    (Complex.continuous_ofReal.tendsto L).comp hqLim
  have hdc : Tendsto (fun Y => d*((r Y/a Y : ℝ) : ℂ)) (𝓝[<] Y₀) (𝓝 (d*(L : ℂ))) :=
    tendsto_const_nhds.mul hqc
  have hcoef : ∀ᶠ Y in 𝓝[<] Y₀,
      ‖d*((r Y/a Y : ℝ) : ℂ)-d*(L : ℂ)‖ < ε/(2*R) := by
    have h := Metric.tendsto_nhds.mp hdc (ε/(2*R)) (by positivity)
    filter_upwards [h] with Y hY
    simpa only [dist_eq_norm] using hY
  have hrSmall : ∀ᶠ Y in 𝓝[<] Y₀, r Y < δ/R :=
    hrLim.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < δ/R))
  have hn0 : ∀ᶠ Y : ℝ in 𝓝 Y₀, |Y-Y₀| < δ := by
    filter_upwards [Metric.ball_mem_nhds Y₀ hδ] with Y hY
    simpa only [Metric.mem_ball,Real.dist_eq] using hY
  have hn : ∀ᶠ Y : ℝ in 𝓝[<] Y₀, |Y-Y₀| < δ := hn0.filter_mono nhdsWithin_le_nhds
  filter_upwards [hAr,hqB,hcoef,hrSmall,hn] with Y hArY hqY hcoefY hrY hnY
  intro w hw
  obtain ⟨haP,hrP⟩ := hArY
  have hnorma : ‖(a Y : ℂ)‖ = a Y := by simp [abs_of_pos haP]
  have hnormr : ‖(r Y : ℂ)‖ = r Y := by simp [abs_of_pos hrP]
  have hz : ‖(r Y : ℂ)*w‖ < δ := by
    calc
      _ = r Y*‖w‖ := by rw [norm_mul,hnormr]
      _ ≤ r Y*R := mul_le_mul_of_nonneg_left hw hrP.le
      _ < δ := (lt_div_iff₀ hR).mp hrY
  have hE := hbound Y ((r Y : ℂ)*w) hnY hz
  have hEdiv : ‖(F Y ((r Y : ℂ)*w)-(a Y : ℂ)-d*((r Y : ℂ)*w))/(a Y : ℂ)‖ ≤
      e*(r Y/a Y)*‖w‖ := by
    rw [norm_div,hnorma]
    calc
      _ ≤ (e*‖(r Y : ℂ)*w‖)/a Y := div_le_div_of_nonneg_right hE haP.le
      _ = _ := by rw [norm_mul,hnormr]; ring
  have haN : (a Y : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt haP
  have heq : F Y ((r Y : ℂ)*w)/(a Y : ℂ)-(1+(d*(L : ℂ))*w) =
      (F Y ((r Y : ℂ)*w)-(a Y : ℂ)-d*((r Y : ℂ)*w))/(a Y : ℂ)+
        (d*((r Y/a Y : ℝ) : ℂ)-d*(L : ℂ))*w := by
    push_cast
    field_simp [haN]
    <;> ring
  have hqLe : r Y/a Y ≤ B := (le_abs_self _).trans hqY.le
  rw [heq]
  calc
    _ ≤ ‖(F Y ((r Y : ℂ)*w)-(a Y : ℂ)-d*((r Y : ℂ)*w))/(a Y : ℂ)‖+
        ‖(d*((r Y/a Y : ℝ) : ℂ)-d*(L : ℂ))*w‖ := norm_add_le _ _
    _ ≤ e*(r Y/a Y)*‖w‖+(ε/(2*R))*‖w‖ := by
      apply add_le_add hEdiv
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hcoefY.le (norm_nonneg w)
    _ ≤ e*B*R+(ε/(2*R))*R := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hqLe he.le) hw (norm_nonneg w) (mul_nonneg he.le hB.le)
      · exact mul_le_mul_of_nonneg_left hw (by positivity)
    _ = ε := by
      dsimp [e]
      field_simp [ne_of_gt hB,ne_of_gt hR]
      <;> ring
end WP.Analysis
