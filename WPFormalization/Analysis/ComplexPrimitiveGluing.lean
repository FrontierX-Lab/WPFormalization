import WPFormalization.Analysis.ComplexGermGluing
/-! Families of true real primitives acquire holomorphic extensions on one
common neighborhood. Disk primitives are fixed by their original real values;
zero-derivative uniqueness and continuity identify them on the closed real
interval. Complex identity glues the germs using radii independent of the
family index. This is ordinary Mathlib complex calculus, with no new inputs. -/
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma exists_common_complex_extension_family {ι : Type*} (a b : ℝ) (v : ι → ℝ → ℂ)
    (hlocal : ∀ x∈Icc a b,∃ r : ℝ,0<r ∧ ∀ k : ι,∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f (Metric.ball (x:ℂ) r) ∧
      ∀ t∈Icc a b,(t:ℂ)∈Metric.ball (x:ℂ) r → f (t:ℂ)=v k t) :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ (∀ x∈Icc a b,(x:ℂ)∈Ω) ∧
      ∃ F : ι → ℂ → ℂ,∀ k : ι,AnalyticOnNhd ℂ (F k) Ω ∧
        ∀ x∈Icc a b,F k (x:ℂ)=v k x := by
  classical
  choose ρ hρ hf using (fun x : Icc a b => hlocal x x.property)
  choose f hfa hfr using hf
  have hcompat (k : ι) (i j : Icc a b) : EqOn (f i k) (f j k)
      (Metric.ball ((i:ℝ):ℂ) (ρ i) ∩ Metric.ball ((j:ℝ):ℂ) (ρ j)) := by
    rcases lt_trichotomy (i:ℝ) (j:ℝ) with hij | hij | hji
    · exact complex_ball_overlap_identity_ordered a b i j (ρ i) (ρ j) i.property j.property hij
        (hρ i) (hρ j) (f i k) (f j k) (v k) (hfa i k) (hfa j k) (hfr i k) (hfr j k)
    · have he : i=j := Subtype.ext hij
      subst j
      exact fun z hz => rfl
    · have he := complex_ball_overlap_identity_ordered a b j i (ρ j) (ρ i) j.property i.property hji
        (hρ j) (hρ i) (f j k) (f i k) (v k) (hfa j k) (hfa i k) (hfr j k) (hfr i k)
      exact fun z hz => (he ⟨hz.2,hz.1⟩).symm
  let Ω : Set ℂ := ⋃ i : Icc a b,Metric.ball ((i:ℝ):ℂ) (ρ i)
  let F : ι → ℂ → ℂ := fun k z => if hz : z∈Ω then f (Classical.choose (mem_iUnion.mp hz)) k z else 0
  have hEq (k : ι) (i : Icc a b) : EqOn (F k) (f i k) (Metric.ball ((i:ℝ):ℂ) (ρ i)) := by
    intro z hz
    have hΩ : z∈Ω := mem_iUnion.mpr ⟨i,hz⟩
    dsimp only [F]
    rw [dite_eq_left hΩ]
    exact hcompat k _ i ⟨Classical.choose_spec (mem_iUnion.mp hΩ),hz⟩
  refine ⟨Ω,isOpen_iUnion (fun i => Metric.isOpen_ball),?_,F,?_⟩
  · intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (hρ ⟨x,hx⟩)⟩
  intro k
  constructor
  · intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    apply (hfa i k z hi).congr
    filter_upwards [Metric.isOpen_ball.mem_nhds hi] with w hw
    exact (hEq k i hw).symm
  · intro x hx
    let i : Icc a b := ⟨x,hx⟩
    have hi : (x:ℂ)∈Metric.ball ((i:ℝ):ℂ) (ρ i) := Metric.mem_ball_self (hρ i)
    exact (hEq k i hi).trans (hfr i k x hx hi)

lemma real_primitive_complex_extension_on_ball (a b : ℝ) (hab : a<b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) (Ω : Set ℂ) (q : ℂ → ℂ) (hq : AnalyticOnNhd ℂ q Ω)
    (hdf : ∀ Y∈Ioo a b,HasDerivAt (fun t : ℝ => (f t:ℂ)) (q (Y:ℂ)) Y)
    (x : ℝ) (hx : x∈Icc a b) (r : ℝ) (hr : 0<r) (hsub : Metric.ball (x:ℂ) r⊆Ω) :
    ∃ G : ℂ → ℂ,AnalyticOnNhd ℂ G (Metric.ball (x:ℂ) r) ∧
      ∀ Y∈Icc a b,(Y:ℂ)∈Metric.ball (x:ℂ) r → G (Y:ℂ)=(f Y:ℂ) := by
  have hqd : DifferentiableOn ℂ q (Metric.ball (x:ℂ) r) := hq.differentiableOn.mono hsub
  obtain ⟨G,hGx,hGd⟩ := hqd.isExactOn_ball.with_val_at (x:ℂ) (f x:ℂ)
  have hGdiff : DifferentiableOn ℂ G (Metric.ball (x:ℂ) r) :=
    fun z hz => (hGd z hz).differentiableAt.differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ G (Metric.ball (x:ℂ) r) := hGdiff.analyticOnNhd Metric.isOpen_ball
  let S : Set ℝ := Ioo a b ∩ Metric.ball x r
  let J : Set ℝ := Icc a b ∩ Metric.ball x r
  have hSopen : IsOpen S := isOpen_Ioo.inter Metric.isOpen_ball
  have hSconn : IsPreconnected S := ((convex_Ioo (𝕜:=ℝ) a b).inter (convex_ball x r)).isPreconnected
  have hSJ : S⊆J := inter_subset_inter_left _ Ioo_subset_Icc_self
  have hJcl : J⊆closure S := by
    intro Y hY
    have hYcl : Y∈closure (Ioo a b) := by rw [closure_Ioo hab.ne];exact hY.1
    rw [mem_closure_iff_nhds] at hYcl ⊢
    intro V hV
    obtain ⟨t,htV,htI⟩ := hYcl (V∩Metric.ball x r) (inter_mem hV (Metric.isOpen_ball.mem_nhds hY.2))
    exact ⟨t,htV.1,htI,htV.2⟩
  let D : ℝ → ℂ := fun Y => G (Y:ℂ)-(f Y:ℂ)
  have hDd (Y : ℝ) (hY : Y∈S) : HasDerivAt D 0 Y := by
    have hYb : (Y:ℂ)∈Metric.ball (x:ℂ) r := by
      simpa only [Metric.mem_ball,complex_dist_ofReal_eq_real] using hY.2
    simpa only [D,Pi.sub_def,sub_self] using (hGd (Y:ℂ) hYb).comp_ofReal.sub (hdf Y hY.1)
  obtain ⟨c,hc⟩ := hSopen.exists_is_const_of_deriv_eq_zero hSconn
    (fun Y hY => (hDd Y hY).differentiableAt.differentiableWithinAt)
    (fun Y hY => (hDd Y hY).deriv)
  have hDc : ContinuousOn D J := by
    apply ContinuousOn.sub
    · intro Y hY
      have hYb : (Y:ℂ)∈Metric.ball (x:ℂ) r := by
        simpa only [Metric.mem_ball,complex_dist_ofReal_eq_real] using hY.2
      exact ((hGa _ hYb).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
    · exact (Complex.continuous_ofReal.comp_continuousOn hf).mono inter_subset_left
  have he : EqOn D (fun _ => c) J :=
    (show EqOn D (fun _ => c) S from hc).of_subset_closure hDc continuousOn_const hSJ hJcl
  have hxJ : x∈J := ⟨hx,Metric.mem_ball_self hr⟩
  have hc0 : c=0 := by
    have hh := he hxJ
    simpa only [D,hGx,sub_self] using hh.symm
  refine ⟨G,hGa,?_⟩
  intro Y hY hYb
  have hYr : Y∈Metric.ball x r := by
    simpa only [Metric.mem_ball,complex_dist_ofReal_eq_real] using hYb
  have hh := he ⟨hY,hYr⟩
  simpa only [D,hc0,sub_eq_zero] using hh

lemma real_primitive_family_common_complex_extension {ι : Type*} (a b : ℝ) (hab : a<b)
    (f : ι → ℝ → ℝ) (hf : ∀ k,ContinuousOn (f k) (Icc a b)) (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y∈Icc a b,(Y:ℂ)∈Ω) (q : ι → ℂ → ℂ) (hq : ∀ k,AnalyticOnNhd ℂ (q k) Ω)
    (hdf : ∀ k,∀ Y∈Ioo a b,HasDerivAt (fun t : ℝ => (f k t:ℂ)) (q k (Y:ℂ)) Y) :
    ∃ U : Set ℂ,IsOpen U ∧ (∀ Y∈Icc a b,(Y:ℂ)∈U) ∧
      ∃ G : ι → ℂ → ℂ,∀ k,AnalyticOnNhd ℂ (G k) U ∧ ∀ Y∈Icc a b,G k (Y:ℂ)=(f k Y:ℂ) := by
  apply exists_common_complex_extension_family a b (fun k Y => (f k Y:ℂ))
  intro x hx
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hΩ (x:ℂ) (hcover x hx)
  refine ⟨r,hr,?_⟩
  intro k
  exact real_primitive_complex_extension_on_ball a b hab (f k) (hf k) Ω (q k) (hq k) (hdf k) x hx r hr hsub
end WP.Analysis
