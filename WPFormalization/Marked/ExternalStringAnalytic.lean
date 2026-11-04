import WPFormalization.Marked.ExternalStringAmplitude
import WPFormalization.Volumes.StringFlowProof
noncomputable section
open Set Filter
open scoped Topology
namespace WP
lemma externalOddWeight_pos (d : List ℕ) : 0 < externalOddWeight d := by
  unfold externalOddWeight
  apply List.prod_pos
  intro x hx
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hx
  exact_mod_cast Nat.pos_of_ne_zero (oddFactorial_ne_zero k)

lemma externalMarkedAmplitude_nonneg (P : PsiTheory) (g : ℕ) {p : ℕ} (hp : 1 ≤ p)
    (q : ℕ) (b : Fin p → ℕ) (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    0 ≤ externalMarkedAmplitude P g q b Y := by
  let d := List.replicate q 0 ++ List.ofFn b
  have hn : 1 ≤ d.length := by simp [d];omega
  have he := normalized_nonneg_nonempty P g d hn Y ⟨hY.1,hY.2.le⟩
  rw [normalized,ite_eq_right (ne_of_lt hY.2)] at he
  have hpos : 0 < a Y ^ complexity g d.length * r Y ^ deficit g d :=
    mul_pos (pow_pos (a_pos Y hY) _) (pow_pos (r_pos Y hY) _)
  have hs : 0 ≤ shifted P g d Y := (mul_nonneg_iff_of_pos_left hpos).mp he
  exact div_nonneg hs (externalOddWeight_pos d).le

lemma externalStringAmplitude_analyticAt (P : PsiTheory) (g : ℕ) {p : ℕ}
    (K : Fin p → ℕ → ℝ → ℝ) (hK : ∀ i n Y, AnalyticAt ℝ (K i n) Y)
    (q : ℕ) (Y : ℝ) (ha : a Y ≠ 0) : AnalyticAt ℝ (externalStringAmplitude P g K q) Y := by
  unfold externalStringAmplitude
  apply Finset.analyticAt_fun_sum
  intro b hb
  apply (externalMarkedAmplitude_analyticAt P g q b Y ha).mul
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact hK i (b i) Y

lemma externalStringAmplitude_nonneg (P : PsiTheory) (g : ℕ) {p : ℕ} (hp : 1 ≤ p)
    (K : Fin p → ℕ → ℝ → ℝ) (hK : ∀ i n Y, 0 ≤ Y → 0 ≤ K i n Y)
    (q : ℕ) (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : 0 ≤ externalStringAmplitude P g K q Y := by
  unfold externalStringAmplitude
  apply Finset.sum_nonneg
  intro b hb
  exact mul_nonneg (externalMarkedAmplitude_nonneg P g hp q b Y hY)
    (Finset.prod_nonneg (fun i _ => hK i (b i) Y hY.1))

lemma externalStringAmplitude_inverse_deriv_germ (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g) {p : ℕ}
    (K : Fin p → ℕ → ℝ → ℝ)
    (hK : ∀ i n Y, HasDerivAt (K i n) (K i (n+1) Y) Y)
    (q : ℕ) (x : ℝ) (hx : x ∈ Ico 0 xCritical) :
    deriv (fun t => externalStringAmplitude P g K q (inverseY t)) =ᶠ[𝓝 x]
      (fun t => externalStringAmplitude P g K (q+1) (inverseY t)) := by
  have hb := inverseY_branch x hx
  have he := Analysis.inverseY_hasDerivAt_eventually_of_lt (inverseY x) hb.1.2
  rw [hb.2] at he
  filter_upwards [he] with t ht
  have hd := (externalStringAmplitude_hasDerivAt P g hg K q (inverseY t) ht.1
    (fun i n => hK i n (inverseY t))).comp t ht.2
  simpa [Function.comp_def,mul_assoc,mul_comm,mul_left_comm,ht.1] using hd.deriv

lemma externalStringAmplitude_positive_egf (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g) {p : ℕ} (hp : 1 ≤ p)
    (K : Fin p → ℕ → ℝ → ℝ)
    (hKa : ∀ i n Y, AnalyticAt ℝ (K i n) Y)
    (hKd : ∀ i n Y, HasDerivAt (K i n) (K i (n+1) Y) Y)
    (hKn : ∀ i n Y, 0 ≤ Y → 0 ≤ K i n Y) :
    (∀ b ∈ Ioo (0:ℝ) xCritical, ENNReal.ofReal b ≤
      (FormalMultilinearSeries.ofScalars ℂ (fun q =>
        ((externalStringAmplitude P g K q 0:ℂ)/(q.factorial:ℂ)))).radius) ∧
    ∀ q : ℕ, ∀ x ∈ Ico 0 xCritical,
      (iteratedDeriv q (FormalMultilinearSeries.ofScalars ℂ (fun q =>
        ((externalStringAmplitude P g K q 0:ℂ)/(q.factorial:ℂ)))).sum (x:ℂ)).re =
        externalStringAmplitude P g K q (inverseY x) := by
  let U : ℕ → ℝ → ℝ := fun q x => externalStringAmplitude P g K q (inverseY x)
  have hf := Analysis.positive_analytic_family_egf U 0 0 le_rfl xCritical Analysis.xCritical_pos_parameter
    (fun q _ x hx => (externalStringAmplitude_analyticAt P g K hKa q (inverseY x)
      (a_pos _ (inverseY_branch x hx).1).ne').comp (Analysis.inverseY_analyticAt_interior x hx))
    (fun q _ x hx => externalStringAmplitude_inverse_deriv_germ P g hg K hKd q x hx)
    (fun q _ x hx => externalStringAmplitude_nonneg P g hp K hKn q (inverseY x) (inverseY_branch x hx).1)
  simpa only [U,Analysis.inverseY_zero_value] using
    (show (∀ b ∈ Ioo (0:ℝ) xCritical, ENNReal.ofReal b ≤
      (FormalMultilinearSeries.ofScalars ℂ (fun q => ((U q 0:ℂ)/(q.factorial:ℂ)))).radius) ∧
      ∀ q : ℕ, ∀ x ∈ Ico 0 xCritical,
      (iteratedDeriv q (FormalMultilinearSeries.ofScalars ℂ (fun q => ((U q 0:ℂ)/(q.factorial:ℂ)))).sum (x:ℂ)).re=U q x from
      ⟨hf.1,fun q x hx => hf.2 q (Nat.zero_le q) x hx⟩)
end WP
namespace WP
lemma externalStringAmplitude_real_hasSum (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g) {p : ℕ} (hp : 1 ≤ p)
    (K : Fin p → ℕ → ℝ → ℝ)
    (hKa : ∀ i n Y, AnalyticAt ℝ (K i n) Y)
    (hKd : ∀ i n Y, HasDerivAt (K i n) (K i (n+1) Y) Y)
    (hKn : ∀ i n Y, 0 ≤ Y → 0 ≤ K i n Y)
    (x : ℝ) (hx : x ∈ Ico 0 xCritical) :
    HasSum (fun q : ℕ => externalStringAmplitude P g K q 0 / (q.factorial:ℝ) * x^q)
      (externalStringAmplitude P g K 0 (inverseY x)) := by
  let S := FormalMultilinearSeries.ofScalars ℂ (fun q =>
    ((externalStringAmplitude P g K q 0:ℂ)/(q.factorial:ℂ)))
  have hf := externalStringAmplitude_positive_egf P g hg hp K hKa hKd hKn
  obtain ⟨b,hxb,hbR⟩ := exists_between hx.2
  have hb : 0 < b := hx.1.trans_lt hxb
  have hmem : (x:ℂ) ∈ Metric.eball (0:ℂ) S.radius := by
    rw [Metric.mem_eball,edist_dist,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hb).mpr hxb) (hf.1 b ⟨hb,hbR⟩)
  have hs := (S.hasSum hmem).mapL Complex.reCLM
  have he := hf.2 0 x hx
  change (S.sum (x:ℂ)).re=externalStringAmplitude P g K 0 (inverseY x) at he
  rw [←he]
  simpa only [S,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,
    ←Complex.ofReal_natCast,←Complex.ofReal_div,←Complex.ofReal_pow,
    ←Complex.ofReal_mul,Complex.reCLM_apply,Complex.ofReal_re] using hs
end WP
