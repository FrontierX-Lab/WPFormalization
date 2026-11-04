import WPFormalization.Volumes.BoundaryPolynomial
import WPFormalization.Geometry.Bridge
import WPFormalization.External.MirzakhaniIntegration
import WPFormalization.RandomGeometry.CutBoundaryProduct

/-! The bounded-boundary volume envelope at every stable topology, including genus zero, derived from the already proved profile comparison. Exact boundary incidence leaves only two factors per physical cut edge. -/

noncomputable section
namespace WP.Critical
open WP Set

lemma cut_volumeModel_pos (P : PsiTheory) (g n : ℕ) (hn : 1 ≤ n) (hs : Stable g n) :
    0<volumeModel P g n := by
  have hz := normalized_pos_valid_nonempty P g (List.replicate n 0)
    (by simpa using hn) (by simpa using hs) (by simp) 0 ⟨le_rfl,y₀_pos.le⟩
  have he := mixedBracket_eq_scaled_normalized_zero P g (List.replicate n 0)
  simp only [List.length_replicate] at he
  rw [volumeModel,he]
  exact mul_pos (by positivity) hz

/-- The bounded-boundary majorant is derived from the already proved profile
comparison at every stable topology, including genus zero. -/
lemma cut_boundaryVolumeModel_envelope (P : PsiTheory) (g n : ℕ)
    (hn : 1 ≤ n) (hs : Stable g n) (L : Fin n→ℝ) :
    boundaryVolumeModel P g n L  ≤  volumeModel P g n*(∏i,boundaryFactor 0 (L i)) := by
  have hp := cut_volumeModel_pos P g n hn hs
  rw [mul_comm (volumeModel P g n)]
  apply (div_le_iff₀ hp).mp
  rw [boundaryVolumeModel_div_eq_profile_sum]
  calc
    _  ≤  ∑d∈degreeTuples g n,boundaryDegreeWeight n L d := by
      apply Finset.sum_le_sum
      intro d hd
      have hprofile := (profile_monotone P g (List.ofFn d)
        (by simpa only [List.length_ofFn] using hs) 0
        (by simpa only [List.length_ofFn] using (show 0<n by omega))
        0 ⟨le_rfl,y₀_pos.le⟩).2.2
      exact mul_le_of_le_one_left (boundaryDegreeWeight_nonneg n L d) hprofile
    _  ≤  ∑'d:Fin n→ℕ,boundaryDegreeWeight n L d :=
      Summable.sum_le_tsum (degreeTuples g n) (fun d _=>boundaryDegreeWeight_nonneg n L d)
        (boundaryDegreeWeight_summable n L)
    _ = _ := boundaryDegreeWeight_tsum n L

universe u v
lemma cut_wpVolume_envelope (P : PsiTheory) (G : WP.External.WeilPeterssonGeometry.{u,v} P)
    (g n : ℕ) (hn : 1 ≤ n) (hs : Stable g n) (L : Fin n→ℝ) (hL : ∀i,0 ≤ L i) :
    WP.External.wpVolume G g n L  ≤  volumeModel P g n*(∏i,boundaryFactor 0 (L i)) := by
  rw [WP.Geometry.wpVolume_eq_boundaryVolumeModel P G g n L hs hL]
  exact cut_boundaryVolumeModel_envelope P g n hn hs L

end WP.Critical
namespace WP.Critical
open Finset

lemma cut_sqrt_budget {ι : Type*} [Fintype ι] (d : ι→ℝ) (hd : ∀i,1 ≤ d i) :
    Real.sqrt (∑i,d i)  ≤  (Fintype.card ι:ℝ)*(∏i,Real.sqrt (d i)) := by
  classical
  have hroot : ∀i,1 ≤ Real.sqrt (d i) := by
    intro i
    rw [←Real.sqrt_one]
    exact Real.sqrt_le_sqrt (hd i)
  have hsum : Real.sqrt (∑i,d i) ≤ ∑i,Real.sqrt (d i) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨sum_nonneg (fun i _=>Real.sqrt_nonneg _),?_⟩
    have hb := sum_sq_le_sq_sum_of_nonneg (s:=univ)
      (f:=fun i=>Real.sqrt (d i)) (fun i _=>Real.sqrt_nonneg _)
    have he : (∑i,Real.sqrt (d i)^2)=(∑i,d i) :=
      sum_congr rfl (fun i _=>Real.sq_sqrt (zero_le_one.trans (hd i)))
    rwa [he] at hb
  refine hsum.trans ?_
  calc
    _  ≤  ∑_i:ι,∏j,Real.sqrt (d j) := sum_le_sum (fun i _=>
      by
        have hb := le_prod_max_one (mem_univ i) (fun j=>Real.sqrt (d j))
        simpa only [max_eq_left (hroot _)] using hb)
    _ = _ := by simp

end WP.Critical
namespace WP.Critical
universe u v w z
open WP.External Finset

lemma cut_volumeProduct_envelope {P : PsiTheory}
    (G : WeilPeterssonGeometry.{u,v} P) {n r : ℕ} (D : MulticurveCutData n r)
    (hs : ∀c,Stable (D.genus c) (D.boundaryCount c))
    (hb : ∀c,1≤D.boundaryCount c) (x : Fin r→ℝ) (hx : ∀e,0≤x e) :
    D.volumeProduct G x ≤
      (∏c:Fin D.components,volumeModel P (D.genus c) (D.boundaryCount c))*
        (∏e:Fin r,boundaryFactor 0 (x e)^2) := by
  have hxp : ∀c i,0≤D.boundaryLengths x c i := by
    intro c i
    unfold MulticurveCutData.boundaryLengths
    split <;> first | exact le_rfl | exact hx _
  have he := prod_le_prod₀
    (fun c (_:c∈univ)=>ENNReal.toReal_nonneg)
    (fun c (_:c∈univ)=>cut_wpVolume_envelope P G (D.genus c) (D.boundaryCount c)
      (hb c) (hs c) (D.boundaryLengths x c) (hxp c))
  unfold MulticurveCutData.volumeProduct
  refine he.trans_eq ?_
  rw [prod_mul_distrib,D.boundaryLengths_prod_of_zero_eq_one
    (fun t:ℝ=>boundaryFactor 0 t) (boundaryFactor_zero_length 0)]

lemma cut_volumeProduct_uniform_boundary_envelope {P : PsiTheory}
    (G : WeilPeterssonGeometry.{u,v} P) (L : ℝ) :
    ∃B:ℝ,0<B ∧ ∀n r:ℕ,∀D:MulticurveCutData n r,
      (∀c,Stable (D.genus c) (D.boundaryCount c)) → (∀c,1≤D.boundaryCount c) →
      ∀x:Fin r→ℝ,(∀e,x e∈Set.Icc 0 L) →
      D.volumeProduct G x ≤
        B^(2*r)*(∏c:Fin D.components,volumeModel P (D.genus c) (D.boundaryCount c)) := by
  obtain ⟨B,hB,hbound⟩ := boundaryFactor_uniform_compact_bound L
  refine ⟨B,hB,?_⟩
  intro n r D hs hb x hx
  have he := cut_volumeProduct_envelope G D hs hb x (fun e=>(hx e).1)
  have hp : (∏e:Fin r,boundaryFactor 0 (x e)^2)≤B^(2*r) := by
    calc
      _ ≤ ∏_e:Fin r,B^2 := by
        apply prod_le_prod₀
        · intro e he;positivity
        · intro e he
          exact pow_le_pow_left₀ (boundaryFactor_pos 0 (x e)).le
            (hbound 0 ⟨le_rfl,y₀_pos.le⟩ (x e) (hx e)) 2
      _ = _ := by simp only [prod_const,card_univ,Fintype.card_fin];rw [←pow_mul]
  have hv : 0≤∏c:Fin D.components,volumeModel P (D.genus c) (D.boundaryCount c) :=
    prod_nonneg (fun c _=>(cut_volumeModel_pos P _ _ (hb c) (hs c)).le)
  exact he.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp hv)

end WP.Critical
