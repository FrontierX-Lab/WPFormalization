import Mathlib

/-! Local holomorphic germs over a real interval glue on one complex open set.
Overlaps contain a real accumulation point; the complex identity principle
proves actual overlap agreement before a choice-based gluing construction.
The implicit extension and derivative restriction lemmas are generic. -/
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace WP.Analysis

lemma exists_complex_implicit_extension (F : ℂ × ℂ → ℂ) (b : ℝ → ℝ) (x₀ : ℝ)
    (hF : ContDiffAt ℂ 1 F ((x₀:ℂ),(b x₀:ℂ)))
    (hInv : (fderiv ℂ F ((x₀:ℂ),(b x₀:ℂ)) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible)
    (hb : ContinuousAt b x₀)
    (hEq : ∀ᶠ x : ℝ in 𝓝 x₀,F ((x:ℂ),(b x:ℂ))=F ((x₀:ℂ),(b x₀:ℂ))) :
    ∃ ψ : ℂ → ℂ,AnalyticAt ℂ ψ (x₀:ℂ) ∧
      ∀ᶠ x : ℝ in 𝓝 x₀,ψ (x:ℂ)=(b x:ℂ) := by
  have hn : (1:ℕ∞ω) ≠ 0 := by norm_num
  let ψ := hF.implicitFunction hn hInv
  have hcψ : ContDiffAt ℂ 1 ψ (x₀:ℂ) := hF.contDiffAt_implicitFunction hn hInv
  have haψ : AnalyticAt ℂ ψ (x₀:ℂ) := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [hcψ.eventually (by norm_num)] with z hz
    exact hz.differentiableAt (by norm_num)
  refine ⟨ψ,haψ,?_⟩
  have he := hF.eventually_apply_eq_iff_implicitFunction hn hInv
  have ht : Tendsto (fun x : ℝ => ((x:ℂ),(b x:ℂ))) (𝓝 x₀)
      (𝓝 ((x₀:ℂ),(b x₀:ℂ))) :=
    Complex.continuous_ofReal.continuousAt.prodMk (Complex.continuous_ofReal.continuousAt.comp hb)
  filter_upwards [ht.eventually he,hEq] with x hx hxEq
  exact hx.mp hxEq

lemma complex_identity_of_real_germ (f g : ℂ → ℂ) (U : Set ℂ) (c : ℝ)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U) (hc : (c:ℂ) ∈ U)
    (he : ∀ᶠ x : ℝ in 𝓝 c,f (x:ℂ)=g (x:ℂ)) : EqOn f g U := by
  have ht : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[≠] c) (𝓝[≠] (c:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [mem_compl_iff,mem_singleton_iff] at hx ⊢
    exact_mod_cast hx
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hU hc
    (ht.frequently (he.filter_mono nhdsWithin_le_nhds).frequently)

lemma complex_dist_ofReal_eq_real (x y : ℝ) : dist (x:ℂ) (y:ℂ)=dist x y := by
  simp only [dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real]

lemma complex_ball_overlap_identity_ordered (a b x y r s : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hxy : x < y) (hr : 0 < r) (hs : 0 < s) (f g : ℂ → ℂ) (v : ℝ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball (x:ℂ) r))
    (hg : AnalyticOnNhd ℂ g (Metric.ball (y:ℂ) s))
    (hfr : ∀ t ∈ Icc a b,(t:ℂ) ∈ Metric.ball (x:ℂ) r → f (t:ℂ)=v t)
    (hgr : ∀ t ∈ Icc a b,(t:ℂ) ∈ Metric.ball (y:ℂ) s → g (t:ℂ)=v t) :
    EqOn f g (Metric.ball (x:ℂ) r ∩ Metric.ball (y:ℂ) s) := by
  intro z hz
  have hden : 0 < r+s := add_pos hr hs
  have hdist : y-x < r+s := by
    have htri := dist_triangle (x:ℂ) z (y:ℂ)
    have h1 : dist (x:ℂ) z < r := by simpa only [Metric.mem_ball,dist_comm] using hz.1
    have h2 : dist z (y:ℂ) < s := hz.2
    rw [complex_dist_ofReal_eq_real,Real.dist_eq,abs_of_neg (sub_neg.mpr hxy)] at htri
    linarith
  let c : ℝ := x+r*(y-x)/(r+s)
  have hcx : c-x=r*(y-x)/(r+s) := by dsimp [c];ring
  have hyc : y-c=s*(y-x)/(r+s) := by dsimp [c];field_simp [hden.ne'];ring
  have hcxp : 0 < c-x := by rw [hcx];exact div_pos (mul_pos hr (sub_pos.mpr hxy)) hden
  have hycp : 0 < y-c := by rw [hyc];exact div_pos (mul_pos hs (sub_pos.mpr hxy)) hden
  have hcxr : c-x < r := by
    rw [hcx]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hycs : y-c < s := by
    rw [hyc]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hcI : c ∈ Ioo a b := ⟨by linarith [hx.1],by linarith [hy.2]⟩
  have hc1 : (c:ℂ) ∈ Metric.ball (x:ℂ) r := by
    rw [Metric.mem_ball,complex_dist_ofReal_eq_real,Real.dist_eq,abs_of_pos hcxp]
    exact hcxr
  have hc2 : (c:ℂ) ∈ Metric.ball (y:ℂ) s := by
    rw [Metric.mem_ball,complex_dist_ofReal_eq_real,Real.dist_eq,abs_of_neg (by linarith : c-y<0)]
    linarith
  have hreal : ∀ᶠ t : ℝ in 𝓝 c,f (t:ℂ)=g (t:ℂ) := by
    have h1 := (Complex.continuous_ofReal.tendsto c).eventually (Metric.isOpen_ball.mem_nhds hc1)
    have h2 := (Complex.continuous_ofReal.tendsto c).eventually (Metric.isOpen_ball.mem_nhds hc2)
    filter_upwards [isOpen_Ioo.mem_nhds hcI,h1,h2] with t ht ht1 ht2
    exact (hfr t ⟨ht.1.le,ht.2.le⟩ ht1).trans (hgr t ⟨ht.1.le,ht.2.le⟩ ht2).symm
  have hconv : Convex ℝ (Metric.ball (x:ℂ) r ∩ Metric.ball (y:ℂ) s) :=
    (convex_ball _ _).inter (convex_ball _ _)
  exact complex_identity_of_real_germ f g _ c (hf.mono inter_subset_left) (hg.mono inter_subset_right)
    hconv.isPreconnected ⟨hc1,hc2⟩ hreal hz

lemma exists_common_complex_extension (a b : ℝ) (v : ℝ → ℂ)
    (hlocal : ∀ x ∈ Icc a b,∃ r : ℝ,0 < r ∧ ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f (Metric.ball (x:ℂ) r) ∧
      ∀ t ∈ Icc a b,(t:ℂ) ∈ Metric.ball (x:ℂ) r → f (t:ℂ)=v t) :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ (∀ x ∈ Icc a b,(x:ℂ) ∈ Ω) ∧
      ∃ F : ℂ → ℂ,AnalyticOnNhd ℂ F Ω ∧ ∀ x ∈ Icc a b,F (x:ℂ)=v x := by
  classical
  choose ρ hρ f hfa hfr using (fun x : Icc a b => hlocal x x.property)
  have hcompat (i j : Icc a b) : EqOn (f i) (f j)
      (Metric.ball ((i:ℝ):ℂ) (ρ i) ∩ Metric.ball ((j:ℝ):ℂ) (ρ j)) := by
    rcases lt_trichotomy (i:ℝ) (j:ℝ) with hij | hij | hji
    · exact complex_ball_overlap_identity_ordered a b i j (ρ i) (ρ j) i.property j.property hij
        (hρ i) (hρ j) (f i) (f j) v (hfa i) (hfa j) (hfr i) (hfr j)
    · have he : i=j := Subtype.ext hij
      subst j
      exact fun z hz => rfl
    · have he := complex_ball_overlap_identity_ordered a b j i (ρ j) (ρ i) j.property i.property hji
        (hρ j) (hρ i) (f j) (f i) v (hfa j) (hfa i) (hfr j) (hfr i)
      exact fun z hz => (he ⟨hz.2,hz.1⟩).symm
  let Ω : Set ℂ := ⋃ i : Icc a b,Metric.ball ((i:ℝ):ℂ) (ρ i)
  let F : ℂ → ℂ := fun z => if hz : z ∈ Ω then f (Classical.choose (mem_iUnion.mp hz)) z else 0
  have hEq (i : Icc a b) : EqOn F (f i) (Metric.ball ((i:ℝ):ℂ) (ρ i)) := by
    intro z hz
    have hΩ : z ∈ Ω := mem_iUnion.mpr ⟨i,hz⟩
    dsimp only [F]
    rw [dite_eq_left hΩ]
    exact hcompat _ i ⟨Classical.choose_spec (mem_iUnion.mp hΩ),hz⟩
  refine ⟨Ω,isOpen_iUnion (fun i => Metric.isOpen_ball),?_,F,?_,?_⟩
  · intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (hρ ⟨x,hx⟩)⟩
  · intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    apply (hfa i z hi).congr
    filter_upwards [Metric.isOpen_ball.mem_nhds hi] with w hw
    exact (hEq i hw).symm
  · intro x hx
    let i : Icc a b := ⟨x,hx⟩
    have hi : (x:ℂ) ∈ Metric.ball ((i:ℝ):ℂ) (ρ i) := Metric.mem_ball_self (hρ i)
    exact (hEq i hi).trans (hfr i x hx hi)

lemma complex_extension_ball_of_real_germ (a b x : ℝ) (v : ℝ → ℂ) (ψ : ℂ → ℂ)
    (ha : AnalyticAt ℂ ψ (x:ℂ))
    (he : ∀ᶠ t : ℝ in 𝓝 x,t ∈ Icc a b → ψ (t:ℂ)=v t) :
    ∃ r : ℝ,0 < r ∧ AnalyticOnNhd ℂ ψ (Metric.ball (x:ℂ) r) ∧
      ∀ t ∈ Icc a b,(t:ℂ) ∈ Metric.ball (x:ℂ) r → ψ (t:ℂ)=v t := by
  obtain ⟨r₁,hr₁,ha⟩ := ha.exists_ball_analyticOnNhd
  obtain ⟨r₂,hr₂,he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min r₁ r₂,lt_min hr₁ hr₂,ha.mono (Metric.ball_subset_ball (min_le_left _ _)),?_⟩
  intro t ht hdist
  have hd : dist t x < min r₁ r₂ := by
    simpa only [Metric.mem_ball,complex_dist_ofReal_eq_real] using hdist
  exact he (hd.trans_le (min_le_right _ _)) ht

lemma complex_deriv_eq_of_real_interval_germ (a b Y β : ℝ) (F : ℂ → ℂ) (v : ℝ → ℝ)
    (hab : a < b) (hY : Y ∈ Icc a b) (hF : DifferentiableAt ℂ F (Y:ℂ))
    (hv : HasDerivAt v β Y)
    (he : (fun t : ℝ => F (t:ℂ)) =ᶠ[𝓝[Icc a b] Y] (fun t => (v t:ℂ))) :
    deriv F (Y:ℂ)=(β:ℂ) := by
  have hu := uniqueDiffOn_Icc hab Y hY
  have h₁ := hF.hasDerivAt.comp_ofReal.hasDerivWithinAt.derivWithin hu
  have h₂ := (hv.ofReal_comp.hasDerivWithinAt.congr_of_eventuallyEq_of_mem he hY).derivWithin hu
  exact h₁.symm.trans h₂

end WP.Analysis
