import WPFormalization.Critical.CutBoundaryEnvelope
import WPFormalization.Critical.CutGraphData
import WPFormalization.Critical.CutBoxIntegral
import WPFormalization.Critical.CutVolumeRatio

/-! Actual ordered-multicurve orbit expectation envelopes from the classical Mirzakhani integration law. These estimates hold at fixed graph size and do not yet sum the full prescribed vertex partition of Lemma G.1. -/
noncomputable section
universe u v w z

namespace WP.Critical
open WP.External MeasureTheory Finset
open scoped ENNReal

lemma cut_orbit_coefficient_le_one {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
    {H:HyperbolicCurveGeometry.{u,v,w} G} (T:MulticurveTopology.{u,v,w,z} G H)
    {g n k:ℕ} (o:T.Orbit g n k) : T.coefficient o≤1 := by
  apply ENNReal.inv_le_one.mpr
  have hindex : (1:ℝ≥0∞)≤(T.cut o).orientationStabilizerIndex := by
    exact_mod_cast (Nat.succ_le_of_lt (T.cut o).orientationStabilizerIndex_pos)
  have hp : (1:ℝ≥0∞)≤2^((T.cut o).oneHandleCount) := one_le_pow₀ (by norm_num)
  simpa only [one_mul] using mul_le_mul' hp hindex

/-- The original Mirzakhani orbit integral is bounded uniformly in all
component genera and cusp allocations of any fixed number of edges. -/
lemma cut_orbit_integral_envelope {P:PsiTheory} (G:WeilPeterssonGeometry.{u,v} P)
    {H:HyperbolicCurveGeometry.{u,v,w} G} (T:MulticurveTopology.{u,v,w,z} G H)
    (MI:MirzakhaniIntegration G H T) (L:ℝ) (hL:0≤L) :
    ∃B:ℝ,0<B ∧ ∀g n k:ℕ,3≤g → 1≤k → ∀o:T.Orbit g n k,
      (∫⁻X,T.orbitSum o (cutLengthTest k L) X ∂G.wpMeasure g n (fun _=>0)) ≤
        ENNReal.ofReal ((B*L)^(2*k)*
          (∏c:Fin (T.cut o).components,volumeModel P ((T.cut o).genus c) ((T.cut o).boundaryCount c))) := by
  obtain ⟨B,hB,hbound⟩ := cut_volumeProduct_uniform_boundary_envelope G L
  refine ⟨B,hB,?_⟩
  intro g n k hg hk o
  have hb : ∀c,1≤(T.cut o).boundaryCount c :=
    CutGraphData.boundaryCount_pos (T.cut o) hk (T.cut_connected o)
  have hvolume : 0≤∏c:Fin (T.cut o).components,
      volumeModel P ((T.cut o).genus c) ((T.cut o).boundaryCount c) :=
    prod_nonneg (fun c _=>(cut_volumeModel_pos P _ _ (hb c) (T.cut_stable o c)).le)
  rw [MI.orbit_integral o (by unfold Stable;omega) (by intro hbad;have he:=congrArg Prod.fst hbad;omega)
    (by intro hbad;have he:=congrArg Prod.fst hbad;omega)
    (cutLengthTest k L) (cutLengthTest_measurable k L)]
  calc
    _ ≤ (1:ℝ≥0∞)*_ := mul_le_mul' (cut_orbit_coefficient_le_one T o) le_rfl
    _ = _ := one_mul _
    _ ≤ ENNReal.ofReal ((B^(2*k)*
        (∏c:Fin (T.cut o).components,volumeModel P ((T.cut o).genus c) ((T.cut o).boundaryCount c)))*L^(2*k)) := by
      apply cut_box_integral_envelope k L _ hL (by positivity)
      intro x hx
      apply hbound n k (T.cut o) (T.cut_stable o) hb x
      exact fun e=>⟨hx.1 e,hx.2 e⟩
    _ = _ := by rw [mul_pow];congr 1;ring

end WP.Critical

namespace WP.Critical
open WP.External MeasureTheory Finset
open scoped ENNReal

lemma cut_orbit_expectation_envelope {P:PsiTheory} (G:WeilPeterssonGeometry.{u,v} P)
    {H:HyperbolicCurveGeometry.{u,v,w} G} (T:MulticurveTopology.{u,v,w,z} G H)
    (MI:MirzakhaniIntegration G H T) (L:ℝ) (hL:0≤L) :
    ∃B:ℝ,0<B ∧ ∀g n k:ℕ,3≤g → 1≤n → 1≤k → ∀o:T.Orbit g n k,
      (∫⁻X,T.orbitSum o (cutLengthTest k L) X ∂wpProbability G g n) ≤
        ENNReal.ofReal (((B*L)^(2*k)*
          (∏c:Fin (T.cut o).components,volumeModel P ((T.cut o).genus c) ((T.cut o).boundaryCount c)))/
            volumeModel P g n) := by
  obtain ⟨B,hB,hbound⟩ := cut_orbit_integral_envelope G T MI L hL
  refine ⟨B,hB,?_⟩
  intro g n k hg hn hk o
  have hs:Stable g n := by unfold Stable;omega
  have hV := cut_volumeModel_pos P g n hn hs
  have he := WP.Geometry.cuspVolume_eq_volumeModel P G g n hs
  unfold cuspVolume wpVolume at he
  have hm:G.wpMeasure g n (fun _=>0) Set.univ=ENNReal.ofReal (volumeModel P g n) := by
    rw [←he]
    exact (ENNReal.ofReal_toReal (G.finite_volume g n _ hs (by simp))).symm
  rw [wpProbability,lintegral_smul_measure,smul_eq_mul,hm]
  refine (mul_le_mul' le_rfl (hbound g n k hg hk o)).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos hV,div_eq_mul_inv]
  exact mul_comm _ _

end WP.Critical

namespace WP.Critical
open WP.External MeasureTheory Finset
open scoped ENNReal

lemma cut_orbit_expectation_gamma_envelope {P:PsiTheory}
    (G:WeilPeterssonGeometry.{u,v} P) {H:HyperbolicCurveGeometry.{u,v,w} G}
    (T:MulticurveTopology.{u,v,w,z} G H) (MI:MirzakhaniIntegration G H T)
    (k Q:ℕ) (hk:1≤k) (hQ:1≤Q) (A L:ℝ) (hA:0<A) (hL:0≤L) :
    ∃C:ℝ,0<C ∧ ∃G₀:ℕ,∀g≥G₀,∀n:ℕ,1≤n → (n:ℝ)≤A*Real.sqrt g →
      ∀o:T.Orbit g n k,(T.cut o).components=Q →
      (∫⁻X,T.orbitSum o (cutLengthTest k L) X ∂wpProbability G g n) ≤
        ENNReal.ofReal (C*(∏c:Fin (T.cut o).components,
          Real.Gamma (complexity ((T.cut o).genus c) ((T.cut o).boundaryCount c)))/
            Real.Gamma (complexity g n)) := by
  obtain ⟨B,hB,hE⟩ := cut_orbit_expectation_envelope G T MI L hL
  obtain ⟨K,hK,G₁,hV⟩ := cut_volume_gamma_ratio P Q hQ A hA
  refine ⟨(1+(B*L)^(2*k))*K,by positivity,max G₁ 3,?_⟩
  intro g hg n hn hcritical o hcomponents
  have hb : ∀c,1≤(T.cut o).boundaryCount c :=
    CutGraphData.boundaryCount_pos (T.cut o) hk (T.cut_connected o)
  have hvc := hV g (by omega) n hcritical
  rw [←hcomponents] at hvc
  specialize hvc (T.cut o).genus (T.cut o).boundaryCount hb (T.cut_stable o)
    (CutGraphData.sum_complexity (T.cut o) (T.cut_stable o) (T.cut_euler o))
  have hΓ : 0≤(∏c:Fin (T.cut o).components,
      Real.Gamma (complexity ((T.cut o).genus c) ((T.cut o).boundaryCount c)))/
        Real.Gamma (complexity g n) := by
    apply div_nonneg
    · apply prod_nonneg
      intro c hc
      apply (Real.Gamma_pos_of_pos _).le
      have hs:=T.cut_stable o c
      unfold Stable complexity at *
      exact_mod_cast (by omega:0<2*(T.cut o).genus c+(T.cut o).boundaryCount c-2)
    · apply (Real.Gamma_pos_of_pos _).le
      have hnat : 0<complexity g n := by unfold complexity;omega
      exact_mod_cast hnat
  refine (hE g n k (by omega) hn hk o).trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ = (B*L)^(2*k)*((∏c:Fin (T.cut o).components,
        volumeModel P ((T.cut o).genus c) ((T.cut o).boundaryCount c))/volumeModel P g n) := by ring
    _ ≤ (B*L)^(2*k)*(K*(∏c:Fin (T.cut o).components,
        Real.Gamma (complexity ((T.cut o).genus c) ((T.cut o).boundaryCount c)))/
          Real.Gamma (complexity g n)) := mul_le_mul_of_nonneg_left hvc (by positivity)
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_right
        (show (B*L)^(2*k)*K≤(1+(B*L)^(2*k))*K by nlinarith) hΓ
      convert he using 1 <;>ring

end WP.Critical
