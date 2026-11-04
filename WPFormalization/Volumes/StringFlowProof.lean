import WPFormalization.Analysis.PositiveAnalyticEGF
import WPFormalization.Analysis.ParameterInverse
import WPFormalization.Intersection.ShiftedStringDerivative
import WPFormalization.Marked.Positivity
import WPFormalization.Statements.Volumes
/-! Actual string-flow identity, Eq. (4.7), and convergence of the original Phi EGF.
The finite shifted background has the proved a*child parameter derivative.
Its composition with the genuine infimum inverse has the derivative family.
Positive stable nonempty children control the Taylor tail; arbitrary finite
prefixes retain the same radius, including the unmarked higher-genus term.
Taylor jets and real analytic uniqueness then identify every stable complex
derivative of the original Phi. All parameter and coefficient identities
are actual definitions; no Phi convergence or string-flow result is assumed.
The actual complex disk also supplies ordinary two-sided markedF derivatives
at Y=0, without differentiating a half-open parameter identity. -/
noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace WP.Analysis
lemma XR_inverseY_eventually_of_lt (Y : ℝ) (hY : Y < y₀) :
    ∀ᶠ x in 𝓝 (XR Y),XR (inverseY x)=x ∧ inverseY x < y₀ := by
  have ha := XR_analyticAt Y
  have hn : deriv XR Y ≠ 0 := by
    rw [(XR_hasDerivAt Y).deriv]
    exact (a_pos_before_y₀ Y hY).ne'
  let ψ := ha.hasStrictDerivAt.localInverse XR (deriv XR Y) Y hn
  have hψ : AnalyticAt ℝ ψ (XR Y) := ha.analyticAt_localInverse hn
  have hψ0 : ψ (XR Y)=Y := (ha.hasStrictDerivAt.eventually_left_inverse hn).self_of_nhds
  have hlt : ∀ᶠ x in 𝓝 (XR Y),ψ x < y₀ := by
    have ht : Tendsto ψ (𝓝 (XR Y)) (𝓝 Y) := by simpa only [hψ0] using hψ.continuousAt.tendsto
    exact ht.eventually (eventually_lt_nhds hY)
  have hr : ∀ᶠ x in 𝓝 (XR Y),XR (ψ x)=x := ha.hasStrictDerivAt.eventually_right_inverse hn
  filter_upwards [hlt,hr] with x hx hrx
  have he := inverseY_eq_of_root x (ψ x) hx.le hrx
  rw [he]
  exact ⟨hrx,hx⟩

lemma inverseY_hasDerivAt_eventually_of_lt (Y : ℝ) (hY : Y < y₀) :
    ∀ᶠ x in 𝓝 (XR Y),a (inverseY x)≠0 ∧
      HasDerivAt inverseY (a (inverseY x))⁻¹ x := by
  filter_upwards [XR_inverseY_eventually_of_lt Y hY] with x hx
  refine ⟨(a_pos_before_y₀ (inverseY x) hx.2).ne',?_⟩
  have hd := (inverseY_analytic_hasDerivAt_of_lt (inverseY x) hx.2).2
  rwa [hx.1] at hd
end WP.Analysis
namespace WP
lemma shifted_inverse_analyticAt (P : PsiTheory) (g p : ℕ) (hs : Stable g p)
    (x : ℝ) (hx : x ∈ Ico 0 xCritical) :
    AnalyticAt ℝ (fun t => shifted P g (List.replicate p 0) (inverseY t)) x := by
  have hy := (inverseY_branch x hx).1
  exact (shifted_zero_analyticAt P g p hs (inverseY x) (a_pos _ hy).ne').comp
    (Analysis.inverseY_analyticAt_interior x hx)

lemma shifted_zero_nonneg_nonempty (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p)
    (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : 0 ≤ shifted P g (List.replicate p 0) Y := by
  have hnorm := normalized_nonneg_nonempty P g (List.replicate p 0)
    (by simpa only [List.length_replicate] using hp) Y ⟨hY.1,hY.2.le⟩
  have hpos : 0 < a Y^(complexity g (List.replicate p 0).length)*
      r Y^(deficit g (List.replicate p 0)) := mul_pos
        (pow_pos (a_pos Y hY) _) (pow_pos (r_pos Y hY) _)
  rw [normalized,ite_eq_right (ne_of_lt hY.2)] at hnorm
  exact (mul_nonneg_iff_of_pos_left hpos).mp hnorm

lemma Phi_eq_shifted_scalar_series (P : PsiTheory) (g : ℕ) :
    Phi P g = (FormalMultilinearSeries.ofScalars ℂ
      (fun n => ((shifted P g (List.replicate n 0) 0:ℂ)/(n.factorial:ℂ)))).sum := by
  funext z
  rw [show (FormalMultilinearSeries.ofScalars ℂ
      (fun n => ((shifted P g (List.replicate n 0) 0:ℂ)/(n.factorial:ℂ)))).sum z =
      ∑' n : ℕ,((shifted P g (List.replicate n 0) 0:ℂ)/(n.factorial:ℂ))*z^n from
    FormalMultilinearSeries.ofScalars_sum_eq _ z]
  apply tsum_congr
  intro n
  dsimp only [Phi,volumeModel,mixedBracket]
  simp only [List.sum_replicate,smul_zero,pow_zero,one_mul,
    deficit,List.length_replicate,List.sum_replicate,Nat.sub_zero]
  push_cast
  field_simp [Real.pi_ne_zero]
end WP
namespace WP
lemma shifted_inverse_deriv_germ (P : PsiTheory) (g : ℕ)
    (p : ℕ) (hs : Stable g p) (x : ℝ) (hx : x ∈ Ico 0 xCritical) :
    deriv (fun t => shifted P g (List.replicate p 0) (inverseY t)) =ᶠ[𝓝 x]
      (fun t => shifted P g (List.replicate (p+1) 0) (inverseY t)) := by
  have hb := inverseY_branch x hx
  have he := Analysis.inverseY_hasDerivAt_eventually_of_lt (inverseY x) hb.1.2
  rw [hb.2] at he
  filter_upwards [he] with t ht
  have hd := (shifted_zero_hasDerivAt P g p hs (inverseY t) ht.1).comp t ht.2
  simpa [Function.comp_def,mul_assoc,mul_comm,mul_left_comm,ht.1] using hd.deriv

def firstStableMarking (g : ℕ) : ℕ := if g=0 then 3 else if g=1 then 1 else 0
lemma firstStableMarking_le_iff (g p : ℕ) : firstStableMarking g ≤ p ↔ Stable g p := by
  unfold firstStableMarking Stable
  split_ifs <;> omega

lemma string_flow_proof (P : PsiTheory) (g : ℕ)
    (n : ℕ) (hs : Stable g n) (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    shifted P g (List.replicate n 0) Y=markedF P g n (XR Y) := by
  let U : ℕ → ℝ → ℝ := fun p t => shifted P g (List.replicate p 0) (inverseY t)
  let s := firstStableMarking g
  have hfamily := Analysis.positive_analytic_family_egf U s (max s 1) (le_max_left _ _)
    xCritical Analysis.xCritical_pos_parameter
    (fun p hp x hx => shifted_inverse_analyticAt P g p ((firstStableMarking_le_iff g p).mp hp) x hx)
    (fun p hp x hx => shifted_inverse_deriv_germ P g p
      ((firstStableMarking_le_iff g p).mp hp) x hx)
    (fun p hp x hx => shifted_zero_nonneg_nonempty P g p ((le_max_right s 1).trans hp)
      (inverseY x) (inverseY_branch x hx).1)
  have hx : XR Y ∈ Ico 0 xCritical := by
    refine ⟨XR_nonneg_interior Y hY,?_⟩
    exact XR_strictMonoOn (show Y ∈ Iic y₀ from hY.2.le) (by simp) hY.2
  have he := hfamily.2 n ((firstStableMarking_le_iff g n).mpr hs) (XR Y) hx
  have hseries : (FormalMultilinearSeries.ofScalars ℂ (fun n => ((U n 0:ℂ)/(n.factorial:ℂ)))).sum = Phi P g := by
    rw [Phi_eq_shifted_scalar_series]
    congr 2
    funext q
    dsimp [U]
    rw [Analysis.inverseY_zero_value]
  rw [hseries] at he
  dsimp only [U] at he
  rw [Analysis.inverseY_eq_of_root _ Y hY.2.le rfl] at he
  exact he.symm
end WP

namespace WP.Analysis
lemma ofReal_le_of_positive_interval_le (R : ℝ) (_hR : 0 < R) (r : ℝ≥0∞)
    (h : ∀ b ∈ Ioo (0:ℝ) R,ENNReal.ofReal b ≤ r) : ENNReal.ofReal R ≤ r := by
  by_cases hr : r=⊤
  · simp [hr]
  apply (ENNReal.ofReal_le_iff_le_toReal hr).mpr
  by_contra hn
  have hrR : r.toReal < R := lt_of_not_ge hn
  obtain ⟨b,hrb,hbR⟩ := exists_between hrR
  have hb : 0 < b := (ENNReal.toReal_nonneg).trans_lt hrb
  have hh := (ENNReal.ofReal_le_iff_le_toReal hr).mp (h b ⟨hb,hbR⟩)
  exact not_le_of_gt hrb hh

lemma scalar_egf_analyticAt_of_radius (c : ℕ → ℝ) (R : ℝ) (hR : 0 < R)
    (hr : ENNReal.ofReal R ≤
      (FormalMultilinearSeries.ofScalars ℂ (fun n => ((c n:ℂ)/(n.factorial:ℂ)))).radius)
    (z : ℂ) (hz : ‖z‖ < R) :
    AnalyticAt ℂ (FormalMultilinearSeries.ofScalars ℂ
      (fun n => ((c n:ℂ)/(n.factorial:ℂ)))).sum z := by
  have hp := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hR) hr
  apply ((FormalMultilinearSeries.ofScalars ℂ
      (fun n => ((c n:ℂ)/(n.factorial:ℂ)))).hasFPowerSeriesOnBall hp).analyticAt_of_mem
  rw [Metric.mem_eball,edist_dist,dist_zero_right]
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hz) hr
end WP.Analysis
namespace WP
lemma shifted_scalar_series_radius (P : PsiTheory) (g : ℕ) :
    ENNReal.ofReal xCritical ≤ (FormalMultilinearSeries.ofScalars ℂ
      (fun n => ((shifted P g (List.replicate n 0) 0:ℂ)/(n.factorial:ℂ)))).radius := by
  let U : ℕ → ℝ → ℝ := fun p t => shifted P g (List.replicate p 0) (inverseY t)
  let s := firstStableMarking g
  have hfamily := Analysis.positive_analytic_family_egf U s (max s 1) (le_max_left _ _)
    xCritical Analysis.xCritical_pos_parameter
    (fun p hp x hx => shifted_inverse_analyticAt P g p ((firstStableMarking_le_iff g p).mp hp) x hx)
    (fun p hp x hx => shifted_inverse_deriv_germ P g p
      ((firstStableMarking_le_iff g p).mp hp) x hx)
    (fun p hp x hx => shifted_zero_nonneg_nonempty P g p ((le_max_right s 1).trans hp)
      (inverseY x) (inverseY_branch x hx).1)
  apply Analysis.ofReal_le_of_positive_interval_le xCritical Analysis.xCritical_pos_parameter
  intro b hb
  simpa only [U,Analysis.inverseY_zero_value] using hfamily.1 b hb

lemma Phi_analyticAt_open_disk (P : PsiTheory) (g : ℕ) (z : ℂ) (hz : ‖z‖ < xCritical) :
    AnalyticAt ℂ (Phi P g) z := by
  rw [Phi_eq_shifted_scalar_series]
  exact Analysis.scalar_egf_analyticAt_of_radius _ xCritical Analysis.xCritical_pos_parameter
    (shifted_scalar_series_radius P g) z hz

lemma Phi_hasSum_shifted (P : PsiTheory) (g : ℕ) (z : ℂ) (hz : ‖z‖ < xCritical) :
    HasSum (fun n : ℕ => (shifted P g (List.replicate n 0) 0:ℂ)/(n.factorial:ℂ)*z^n) (Phi P g z) := by
  let p := FormalMultilinearSeries.ofScalars ℂ
    (fun n => ((shifted P g (List.replicate n 0) 0:ℂ)/(n.factorial:ℂ)))
  have hr := shifted_scalar_series_radius P g
  have hmem : z ∈ Metric.eball (0:ℂ) p.radius := by
    rw [Metric.mem_eball,edist_dist,dist_zero_right]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff Analysis.xCritical_pos_parameter).mpr hz) hr
  have hsum := p.hasSum hmem
  have he : Phi P g z=p.sum z := congrFun (Phi_eq_shifted_scalar_series P g) z
  rw [←he] at hsum
  simpa only [p,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul] using hsum
end WP
namespace WP
lemma markedF_parameter_hasDerivAt (P : PsiTheory) (g p : ℕ) (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    HasDerivAt (fun t : ℝ => markedF P g p (XR t))
      (a Y*markedF P g (p+1) (XR Y)) Y := by
  have hx : ‖(XR Y:ℂ)‖ < xCritical := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (XR_nonneg_interior Y hY)]
    exact XR_strictMonoOn (show Y ∈ Iic y₀ from hY.2.le) (by simp) hY.2
  have hp : AnalyticAt ℂ (iteratedDeriv p (Phi P g)) (XR Y:ℂ) := by
    simpa only [iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P g _ hx).iterated_deriv p
  have hd := hp.differentiableAt.hasDerivAt.real_of_complex.comp Y (XR_hasDerivAt Y)
  simpa only [Function.comp_def,markedF,iteratedDeriv_succ,mul_comm] using hd
end WP
namespace WP
lemma shifted_zero_pos_nonempty (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : 0 < shifted P g (List.replicate p 0) Y := by
  have hn := normalized_pos_valid_nonempty P g (List.replicate p 0)
    (by simpa only [List.length_replicate] using hp)
    (by simpa only [List.length_replicate] using hs) (by simp) Y ⟨hY.1,hY.2.le⟩
  rw [normalized,ite_eq_right (ne_of_lt hY.2)] at hn
  have hfac : 0 < a Y^(complexity g (List.replicate p 0).length)*
      r Y^(deficit g (List.replicate p 0)) := mul_pos
        (pow_pos (a_pos Y hY) _) (pow_pos (r_pos Y hY) _)
  exact (mul_pos_iff_of_pos_left hfac).mp hn
lemma markedF_pos_parameter (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : 0 < markedF P g p (XR Y) := by
  rw [←string_flow_proof P g p hs Y hY]
  exact shifted_zero_pos_nonempty P g p hp hs Y hY
lemma markedF_parameter_log_hasDerivAt (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    HasDerivAt (fun t : ℝ => Real.log (markedF P g p (XR t)))
      (a Y*markedF P g (p+1) (XR Y)/markedF P g p (XR Y)) Y :=
  (markedF_parameter_hasDerivAt P g p Y hY).log (markedF_pos_parameter P g p hp hs Y hY).ne'
end WP
