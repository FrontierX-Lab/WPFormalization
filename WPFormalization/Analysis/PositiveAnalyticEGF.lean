import Mathlib
/-! Positive real Taylor coefficients control a genuine complex EGF.
Taylor with a nonnegative remainder gives geometric coefficient bounds;
finite coefficient prefixes preserve the radius. Complex derivatives are
identified with a real analytic derivative family by their actual origin
jets and the identity principle on connected intervals. No convergence or
family identification is assumed as an external result. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma positive_taylor_coefficient_bound (f : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (ha : AnalyticOnNhd ℝ f (Icc 0 b))
    (hn : ∀ n : ℕ, ∀ x ∈ Icc 0 b, 0 ≤ iteratedDeriv n f x) (n : ℕ) :
    0 ≤ iteratedDeriv n f 0/(n.factorial:ℝ) ∧
      iteratedDeriv n f 0/(n.factorial:ℝ)*b^n ≤ f b := by
  have h0 : (0:ℝ) ∈ Icc 0 b := ⟨le_rfl,hb.le⟩
  have hu : UniqueDiffOn ℝ (uIcc (0:ℝ) b) := uniqueDiffOn_uIcc hb.ne
  have hc : ContDiffOn ℝ (n+1) f (uIcc (0:ℝ) b) := by
    intro x hx
    rw [uIcc_of_le hb.le] at hx
    exact (ha x hx).contDiffAt.contDiffWithinAt
  obtain ⟨x,hx,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hb.ne hc
  have heval : taylorWithinEval f n (uIcc (0:ℝ) b) 0 b =
      ∑ k ∈ Finset.range (n+1),iteratedDeriv k f 0/(k.factorial:ℝ)*b^k := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [taylorCoeffWithin]
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (ha 0 h0).contDiffAt
      (by simpa only [uIcc_of_le hb.le] using h0)]
    simp only [sub_zero]
    ring
  have hrem : 0 ≤ f b-taylorWithinEval f n (uIcc (0:ℝ) b) 0 b := by
    rw [he]
    have hx' : x ∈ Icc (0:ℝ) b := by
      rw [uIoo_of_lt hb] at hx
      exact ⟨hx.1.le,hx.2.le⟩
    exact div_nonneg (mul_nonneg (hn _ x hx') (pow_nonneg (by simpa using hb.le) _))
      (Nat.cast_nonneg _)
  have hsingle := Finset.single_le_sum (f:=fun k : ℕ => iteratedDeriv k f 0/(k.factorial:ℝ)*b^k)
    (fun k hk => mul_nonneg (div_nonneg (hn k 0 h0) (Nat.cast_nonneg _)) (pow_nonneg hb.le _))
    (Finset.mem_range.mpr (Nat.lt_succ_self n))
  refine ⟨div_nonneg (hn n 0 h0) (Nat.cast_nonneg _),?_⟩
  rw [heval] at hrem
  linarith

lemma positive_taylor_complex_radius (f : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (ha : AnalyticOnNhd ℝ f (Icc 0 b))
    (hn : ∀ n : ℕ, ∀ x ∈ Icc 0 b, 0 ≤ iteratedDeriv n f x) :
    (ENNReal.ofReal b) ≤
      (FormalMultilinearSeries.ofScalars ℂ (fun n => ((iteratedDeriv n f 0/(n.factorial:ℝ):ℝ):ℂ))).radius := by
  rw [ENNReal.ofReal_eq_coe_nnreal hb.le]
  apply FormalMultilinearSeries.le_radius_of_bound _ (f b)
  intro n
  rw [FormalMultilinearSeries.ofScalars_norm,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (positive_taylor_coefficient_bound f b hb ha hn n).1]
  exact (positive_taylor_coefficient_bound f b hb ha hn n).2

end WP.Analysis
namespace WP.Analysis
lemma iteratedDeriv_family_germ (U : ℕ → ℝ → ℝ) (x : ℝ)
    (hd : ∀ p : ℕ, deriv (U p) =ᶠ[𝓝 x] U (p+1)) (p n : ℕ) :
    iteratedDeriv n (U p) =ᶠ[𝓝 x] U (p+n) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero,Nat.add_zero];rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv.trans (by simpa only [Nat.add_assoc] using hd (p+n))

lemma scalar_series_iteratedDeriv_zero (c : ℕ → ℝ)
    (hp : 0 < (FormalMultilinearSeries.ofScalars ℂ (fun n => ((c n:ℂ)/(n.factorial:ℂ)))).radius)
    (n : ℕ) :
    iteratedDeriv n (FormalMultilinearSeries.ofScalars ℂ (fun n => ((c n:ℂ)/(n.factorial:ℂ)))).sum 0 = (c n:ℂ) := by
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => ((c n:ℂ)/(n.factorial:ℂ)))
  have hf := (p.hasFPowerSeriesOnBall hp).factorial_smul (1:ℂ) n
  rw [←iteratedDeriv_eq_iteratedFDeriv] at hf
  calc
    _ = (n.factorial:ℂ)*((c n:ℂ)/(n.factorial:ℂ)) := by
      simpa [p,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,nsmul_eq_mul] using hf.symm
    _ = _ := by
      have hn : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp [hn]

lemma iteratedDeriv_iteratedDeriv_eq {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (f : 𝕜 → 𝕜) (p n : ℕ) : iteratedDeriv n (iteratedDeriv p f) = iteratedDeriv (n+p) f := by
  simp only [iteratedDeriv_eq_iterate,Function.iterate_add_apply]

lemma real_restriction_analyticAt (f : ℂ → ℂ) (x : ℝ) (hf : AnalyticAt ℂ f (x:ℂ)) :
    AnalyticAt ℝ (fun y : ℝ => (f y).re) x := by
  exact (Complex.reCLM.analyticAt _).comp
    ((hf.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt _))

lemma real_restriction_iteratedDeriv_germ (f : ℂ → ℂ) (x : ℝ)
    (hf : AnalyticAt ℂ f (x:ℂ)) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => (f y).re) =ᶠ[𝓝 x]
      (fun y : ℝ => (iteratedDeriv n f y).re) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero];rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    apply ih.deriv.trans
    have ha : AnalyticAt ℂ (iteratedDeriv n f) (x:ℂ) := by
      simpa only [iteratedDeriv_eq_iterate] using hf.iterated_deriv n
    have he := (Complex.continuous_ofReal.tendsto x).eventually ha.eventually_analyticAt
    filter_upwards [he] with y hy
    simpa only [iteratedDeriv_succ] using (hy.differentiableAt.hasDerivAt.real_of_complex).deriv

lemma analytic_eventuallyEq_of_iteratedDeriv_eq (f g : ℝ → ℝ)
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0)
    (hj : ∀ n : ℕ, iteratedDeriv n f 0 = iteratedDeriv n g 0) :
    f =ᶠ[𝓝 0] g := by
  have he : FormalMultilinearSeries.ofScalars ℝ (fun n => iteratedDeriv n f 0/(n.factorial:ℝ)) =
      FormalMultilinearSeries.ofScalars ℝ (fun n => iteratedDeriv n g 0/(n.factorial:ℝ)) := by
    congr 1
    funext n
    rw [hj]
  have hfs := hf.hasFPowerSeriesAt.eventually_hasSum
  rw [he] at hfs
  filter_upwards [hfs,hg.hasFPowerSeriesAt.eventually_hasSum] with y hy hy'
  simpa only [zero_add] using hy.unique hy'
end WP.Analysis
namespace WP.Analysis
lemma scalar_egf_derivative_identification (c : ℕ → ℝ) (f : ℝ → ℝ) (k : ℕ)
    (b x : ℝ) (hb : 0 < b) (hx : x ∈ Ico 0 b)
    (hr : ENNReal.ofReal b ≤
      (FormalMultilinearSeries.ofScalars ℂ (fun n => ((c n:ℂ)/(n.factorial:ℂ)))).radius)
    (ha : AnalyticOnNhd ℝ f (Icc 0 x))
    (hj : ∀ n : ℕ,iteratedDeriv n f 0=c (n+k)) :
    (iteratedDeriv k (FormalMultilinearSeries.ofScalars ℂ
      (fun n => ((c n:ℂ)/(n.factorial:ℂ)))).sum (x:ℂ)).re=f x := by
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => ((c n:ℂ)/(n.factorial:ℂ)))
  have hp : 0 < p.radius := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hb) hr
  have hseries := p.hasFPowerSeriesOnBall hp
  have hc (y : ℝ) (hy : y ∈ Icc 0 x) : AnalyticAt ℂ p.sum (y:ℂ) := by
    apply hseries.analyticAt_of_mem
    rw [Metric.mem_eball]
    have he : edist (y:ℂ) 0=ENNReal.ofReal y := by
      simp [edist_dist,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hy.1]
    rw [he]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hb).mpr (hy.2.trans_lt hx.2)) hr
  let G : ℝ → ℝ := fun y => (iteratedDeriv k p.sum y).re
  have hG : AnalyticOnNhd ℝ G (Icc 0 x) := by
    intro y hy
    apply real_restriction_analyticAt
    simpa only [iteratedDeriv_eq_iterate] using (hc y hy).iterated_deriv k
  have h0 : (0:ℝ) ∈ Icc 0 x := ⟨le_rfl,hx.1⟩
  have hGjets (n : ℕ) : iteratedDeriv n G 0=iteratedDeriv n f 0 := by
    have hk : AnalyticAt ℂ (iteratedDeriv k p.sum) ((0:ℝ):ℂ) := by
      simpa only [iteratedDeriv_eq_iterate] using (hc 0 h0).iterated_deriv k
    rw [(real_restriction_iteratedDeriv_germ _ 0 hk n).self_of_nhds]
    dsimp only
    rw [iteratedDeriv_iteratedDeriv_eq,Complex.ofReal_zero]
    rw [scalar_series_iteratedDeriv_zero c hp,hj,Complex.ofReal_re]
  have he := analytic_eventuallyEq_of_iteratedDeriv_eq G f (hG 0 h0) (ha 0 h0) hGjets
  exact (hG.eqOn_of_preconnected_of_eventuallyEq ha isPreconnected_Icc h0 he) ⟨hx.1,le_rfl⟩
end WP.Analysis
namespace WP.Analysis
lemma positive_taylor_tail_complex_radius (c : ℕ → ℝ) (f : ℝ → ℝ) (k : ℕ)
    (b : ℝ) (hb : 0 < b) (ha : AnalyticOnNhd ℝ f (Icc 0 b))
    (hn : ∀ n : ℕ, ∀ x ∈ Icc 0 b,0 ≤ iteratedDeriv n f x)
    (hc : ∀ n : ℕ,c (n+k)=iteratedDeriv n f 0) :
    ENNReal.ofReal b ≤
      (FormalMultilinearSeries.ofScalars ℂ (fun n => ((c n:ℂ)/(n.factorial:ℂ)))).radius := by
  rw [ENNReal.ofReal_eq_coe_nnreal hb.le]
  let H : ℝ := ∑ j ∈ Finset.range k,|c j|/(j.factorial:ℝ)*b^j
  have hH : 0 ≤ H := Finset.sum_nonneg (fun j hj =>
    mul_nonneg (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hb.le _))
  have hfb : 0 ≤ f b := by simpa only [iteratedDeriv_zero] using hn 0 b ⟨hb.le,le_rfl⟩
  have htail : 0 ≤ f b*b^k := mul_nonneg hfb (pow_nonneg hb.le _)
  apply FormalMultilinearSeries.le_radius_of_bound _ (H+f b*b^k)
  intro n
  rw [FormalMultilinearSeries.ofScalars_norm,norm_div,Complex.norm_real,
    Complex.norm_natCast,Real.norm_eq_abs]
  by_cases hnk : n < k
  · exact (Finset.single_le_sum (f := fun j : ℕ => |c j|/(j.factorial:ℝ)*b^j) (fun j hj =>
      mul_nonneg (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hb.le _))
      (Finset.mem_range.mpr hnk)).trans (le_add_of_nonneg_right htail)
  · obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_gt hnk)
    rw [Nat.add_comm k m,hc]
    have hnum : 0 ≤ iteratedDeriv m f 0 := hn m 0 ⟨le_rfl,hb.le⟩
    rw [abs_of_nonneg hnum]
    have hfac : (m.factorial:ℝ) ≤ ((m+k).factorial:ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_add_right m k)
    have hd : iteratedDeriv m f 0/((m+k).factorial:ℝ) ≤ iteratedDeriv m f 0/(m.factorial:ℝ) :=
      div_le_div_of_nonneg_left hnum (by positivity) hfac
    calc
      _ ≤ iteratedDeriv m f 0/(m.factorial:ℝ)*b^(m+k) :=
        mul_le_mul_of_nonneg_right hd (pow_nonneg hb.le _)
      _ = (iteratedDeriv m f 0/(m.factorial:ℝ)*b^m)*b^k := by rw [pow_add];ring
      _ ≤ f b*b^k := mul_le_mul_of_nonneg_right
        (positive_taylor_coefficient_bound f b hb ha hn m).2 (pow_nonneg hb.le _)
      _ ≤ _ := le_add_of_nonneg_left hH
end WP.Analysis
namespace WP.Analysis
lemma stable_family_iteratedDeriv (U : ℕ → ℝ → ℝ) (k : ℕ) (R : ℝ)
    (hd : ∀ p ≥ k, ∀ x ∈ Ico 0 R,deriv (U p) =ᶠ[𝓝 x] U (p+1))
    (p : ℕ) (hp : k ≤ p) (x : ℝ) (hx : x ∈ Ico 0 R) (n : ℕ) :
    iteratedDeriv n (U p) x=U (p+n) x := by
  have hflow : ∀ q : ℕ,deriv (fun y => U (p+q) y) =ᶠ[𝓝 x] (fun y => U (p+(q+1)) y) := by
    intro q
    simpa only [Nat.add_assoc] using hd (p+q) (by omega) x hx
  have he := (iteratedDeriv_family_germ (fun q => U (p+q)) x hflow 0 n).self_of_nhds
  simpa only [Nat.add_zero,Nat.zero_add] using he

lemma positive_analytic_family_egf (U : ℕ → ℝ → ℝ) (s k : ℕ) (hsk : s ≤ k)
    (R : ℝ) (hR : 0 < R)
    (ha : ∀ p ≥ s,AnalyticOnNhd ℝ (U p) (Ico 0 R))
    (hd : ∀ p ≥ s,∀ x ∈ Ico 0 R,deriv (U p) =ᶠ[𝓝 x] U (p+1))
    (hn : ∀ p ≥ k,∀ x ∈ Ico 0 R,0 ≤ U p x)
    :
    (∀ b ∈ Ioo (0:ℝ) R,ENNReal.ofReal b ≤
      (FormalMultilinearSeries.ofScalars ℂ (fun n => ((U n 0:ℂ)/(n.factorial:ℂ)))).radius) ∧
    ∀ p ≥ s,∀ x ∈ Ico (0:ℝ) R,
      (iteratedDeriv p (FormalMultilinearSeries.ofScalars ℂ
        (fun n => ((U n 0:ℂ)/(n.factorial:ℂ)))).sum (x:ℂ)).re=U p x := by
  have hcoeff (b : ℝ) (hb : b ∈ Ioo (0:ℝ) R) : ENNReal.ofReal b ≤
      (FormalMultilinearSeries.ofScalars ℂ (fun n => ((U n 0:ℂ)/(n.factorial:ℂ)))).radius := by
    apply positive_taylor_tail_complex_radius (fun n => U n 0) (U k) k b hb.1
    · exact fun x hx => ha k hsk x ⟨hx.1,hx.2.trans_lt hb.2⟩
    · intro n x hx
      rw [stable_family_iteratedDeriv U s R hd k hsk x ⟨hx.1,hx.2.trans_lt hb.2⟩ n]
      exact hn (k+n) (by omega) x ⟨hx.1,hx.2.trans_lt hb.2⟩
    · intro n
      rw [stable_family_iteratedDeriv U s R hd k hsk 0 ⟨le_rfl,hR⟩ n,Nat.add_comm]
  refine ⟨hcoeff,?_⟩
  intro p hp x hx
  obtain ⟨b,hxb,hbR⟩ := exists_between hx.2
  have hb : 0 < b := hx.1.trans_lt hxb
  apply scalar_egf_derivative_identification (fun n => U n 0) (U p) p b x hb
    ⟨hx.1,hxb⟩ (hcoeff b ⟨hb,hbR⟩)
  · exact fun y hy => ha p hp y ⟨hy.1,hy.2.trans_lt hx.2⟩
  · intro n
    rw [stable_family_iteratedDeriv U s R hd p hp 0 ⟨le_rfl,hR⟩ n,Nat.add_comm]
end WP.Analysis
