import WPFormalization.RandomGeometry.GeneralPlanarTypeTail
import WPFormalization.RandomGeometry.PantsMomentAsymptoticsConcentration

/-! Uniform disappearance of large planar cusp types on the original
primitive scale. No bounded-density or positive limiting saddle is assumed. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter
open scoped Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

lemma primitive_planar_size_eventually (n : ℕ→ℕ) (hn : Tendsto n atTop atTop) (A : ℝ) :
    Filter.Eventually (fun g : ℕ => A ≤ min (2*(g:ℝ)-1) ((n g-1:ℕ):ℝ)) atTop := by
  let B : ℕ := Nat.ceil (A+1)
  have hB : A+1≤(B:ℝ) := Nat.le_ceil _
  filter_upwards [eventually_ge_atTop B,hn.eventually_ge_atTop (B+1)] with g hg hng
  have hgr : (B:ℝ)≤g := by exact_mod_cast hg
  have hnr : (B:ℝ)≤((n g-1:ℕ):ℝ) := by exact_mod_cast (show B≤n g-1 by omega)
  apply le_min <;> linarith

include C MI in
theorem generalPlanar_type_tail_mean_uniform (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (t : ℝ) (ht : 0≤t) :
    ∀ε : ℝ,0<ε→∃K₀ : ℕ,∀ᶠ g in (atTop : Filter ℕ), ∀ K : ℕ,K₀≤K→
      (∫X : G.Moduli g (n g) (fun _=>0),
        (generalPlanarTypeTailCount H X K (t/Real.sqrt (primitivePlanarEffectiveScale g (n g))):ℝ)
          ∂wpProbability G g (n g))≤ε := by
  intro ε hε
  have hninf := pants_fast_cusps_tendsto_atTop n hn
  obtain ⟨A,hA,hbase⟩ := primitive_planar_first_base_type_tail P
  let B : ℝ := 6*Real.exp 1*t^2+1
  have hB : 0<B := by dsimp [B];positivity
  obtain ⟨K₀,hK₀⟩ := primitive_planar_type_tail_uniform P (ε/B) (div_pos hε hB)
  refine ⟨K₀,?_⟩
  have hL := primitive_planar_rescaled_length_tendsto_zero n hn t
  have hcollar : 0<2*Real.arsinh 1 :=
    mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (by norm_num))
  filter_upwards [eventually_ge_atTop (2:ℕ),hninf.eventually_ge_atTop 2,
    primitive_planar_size_eventually n hninf A,
    primitive_coefficient_ratio_eventually P n hninf,
    hL.eventually (gt_mem_nhds hcollar),hL.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
    with g hg hng hsize hx hLg hLone
  intro K hK
  have hL0 : 0≤t/Real.sqrt (primitivePlanarEffectiveScale g (n g)) :=
    div_nonneg ht (Real.sqrt_nonneg _)
  have hxclosed : primitiveSaddleX g (n g)∈Icc (0:ℝ) xCritical := ⟨hx.1.1.le,hx.1.2.le⟩
  have hb := hbase g (n g) hg hng hsize K t
  have hmean := generalPlanar_type_tail_mean_upper H T C MI hg hng K _ hL0 hLg
  have hnonneg := (primitive_planar_type_tail_le_critical P K _ hxclosed).1
  calc
    _≤Real.exp (t/Real.sqrt (primitivePlanarEffectiveScale g (n g)))*
        (6*t^2*primitivePlanarTypeTail P K (primitiveSaddleX g (n g))) :=
      hmean.trans (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le)
    _≤B*primitivePlanarTypeTail P K (primitiveSaddleX g (n g)) := by
      rw [show Real.exp (t/Real.sqrt (primitivePlanarEffectiveScale g (n g)))*
        (6*t^2*primitivePlanarTypeTail P K (primitiveSaddleX g (n g)))=
        (6*Real.exp (t/Real.sqrt (primitivePlanarEffectiveScale g (n g)))*t^2)*
          primitivePlanarTypeTail P K (primitiveSaddleX g (n g)) by ring]
      apply mul_le_mul_of_nonneg_right _ hnonneg
      have he := Real.exp_le_exp.mpr hLone.le
      dsimp [B]
      nlinarith [sq_nonneg t]
    _≤B*(ε/B) := mul_le_mul_of_nonneg_left (hK₀ K hK _ hxclosed) hB.le
    _=ε := mul_div_cancel₀ _ hB.ne'

include C MI in
theorem generalPlanar_type_tail_probability_uniform (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (t : ℝ) (ht : 0≤t) :
    ∀ε : ℝ,0<ε→∃K₀ : ℕ,∀ᶠ g in (atTop : Filter ℕ), ∀ K : ℕ,K₀≤K→
      (wpProbability G g (n g)).real
        {X | 0<generalPlanarTypeTailCount H X K
          (t/Real.sqrt (primitivePlanarEffectiveScale g (n g)))}≤ε := by
  intro ε hε
  obtain ⟨K₀,hK₀⟩ := generalPlanar_type_tail_mean_uniform H T C MI n hn t ht ε hε
  refine ⟨K₀,?_⟩
  have hL := primitive_planar_rescaled_length_tendsto_zero n hn t
  have hcollar : 0<2*Real.arsinh 1 :=
    mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (by norm_num))
  filter_upwards [hK₀,eventually_ge_atTop (1:ℕ),hL.eventually (gt_mem_nhds hcollar)]
    with g hkg hg hLg
  intro K hK
  exact (generalPlanar_type_tail_probability_le_mean H T C MI hg K _ hLg).trans (hkg K hK)

end WP.RandomGeometry
