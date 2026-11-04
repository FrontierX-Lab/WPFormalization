import WPFormalization.Volumes.RatioModelActualSaddles
import WPFormalization.Volumes.RatioQLogAlgebra
import WPFormalization.Analysis.VolumeProfileRegular

/-! The actual coefficient-extraction model in the inverse-genus cusp ratio.
The two distinct saddles, Poisson factor, finite complexity and variance are
kept exactly. The logarithmic saddle estimates are the proved physical-model
estimates; the zero-degree branch is an exact square-root identity. -/
noncomputable section

namespace WP.Analysis
open Set Filter
open scoped Topology

lemma ratioQ_saddle_spec (h k : ℝ) (hh : 0 < h) (hk : 0 < k) :
    let Y := densityY (2*k/h)
    Y ∈ Ioo (0:ℝ) y₀ ∧ h*Psi (XR Y)=k := by
  dsimp only
  have hs := densityY_spec (2*k/h) (by positivity)
  have hp : 0 < densityY (2*k/h) := by
    by_contra hn
    have hz : densityY (2*k/h)=0 := le_antisymm (not_lt.mp hn) hs.1.1
    rw [hz,density_zero_value] at hs
    have hd : 0 < 2*k/h := by positivity
    linarith [hs.2]
  refine ⟨⟨hp,hs.1.2⟩,?_⟩
  rw [Psi,inverseY_eq_of_root _ _ hs.1.2.le rfl,hs.2]
  field_simp

lemma ratioQ_saddle_pair (h k : ℝ) (hh : 0 < h) (hk : 0 < k) :
    let Y := densityY (2*k/h)
    let Y' := densityY (2*k/(h+1))
    Y' ∈ Ioo (0:ℝ) y₀ ∧ Y ∈ Ioo (0:ℝ) y₀ ∧ Y'≤Y ∧
      h*Psi (XR Y)=k ∧ (h+1)*Psi (XR Y')=k := by
  dsimp only
  have hs := ratioQ_saddle_spec h k hh hk
  have hs' := ratioQ_saddle_spec (h+1) k (by positivity) hk
  have hd := densityY_spec (2*k/h) (by positivity)
  have hd' := densityY_spec (2*k/(h+1)) (by positivity)
  refine ⟨hs'.1,hs.1,?_,hs.2,hs'.2⟩
  apply (density_strictMonoOn.le_iff_le hd'.1 hd.1).mp
  rw [hd'.2,hd.2]
  exact div_le_div_of_nonneg_left (by positivity) hh (by linarith)

lemma ratioQ_pos (g p k : ℕ) (hs : Stable g p) : 0 < extractionQ g p k := by
  have hh : 0 < (complexity g p:ℝ) := by
    exact_mod_cast (show 0 < complexity g p by unfold Stable at hs;unfold complexity;omega)
  have hY := (densityY_spec (2*(k:ℝ)/(complexity g p:ℝ)) (by positivity)).1
  have hM := markedModel_pos_parameter g p hs _ hY
  unfold extractionQ
  dsimp only
  split_ifs with hk
  · positivity
  · have hkp : 0 < (k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hYs := (ratioQ_saddle_spec (complexity g p) k hh hkp).1
    have hx : 0 < XR (densityY (2*(k:ℝ)/(complexity g p:ℝ))) := by
      simpa only [XR_zero] using XR_strictMonoOn y₀_pos.le hY.2.le hYs.1
    have hv := ratioSaddle_variance_pos _ hYs
    have hp : 0 < poissonCenter k := by unfold poissonCenter;positivity
    positivity

lemma ratioQ_log_exact (g p k : ℕ) (hs : Stable g p) (hk : 1 ≤ k) :
    let h : ℝ := complexity g p
    let Y := densityY (2*(k:ℝ)/h)
    Real.log (extractionQ g p k) =
      Real.log (markedModel g p Y)-Real.log Real.pi-(k:ℝ)*Real.log (XR Y)+
        Real.log (poissonCenter k)+
        (1/2)*(Real.log (k:ℝ)-Real.log h-Real.log (euler Psi (XR Y))) := by
  dsimp only
  have hh : 0 < (complexity g p:ℝ) := by
    exact_mod_cast (show 0 < complexity g p by unfold Stable at hs;unfold complexity;omega)
  have hkp : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hY := (ratioQ_saddle_spec (complexity g p) k hh hkp).1
  have hx : 0 < XR (densityY (2*(k:ℝ)/(complexity g p:ℝ))) := by
    simpa only [XR_zero] using XR_strictMonoOn y₀_pos.le hY.2.le hY.1
  have hv := ratioSaddle_variance_pos _ hY
  have hM := markedModel_pos_parameter g p hs _ ⟨hY.1.le,hY.2⟩
  have hp : 0 < poissonCenter k := by unfold poissonCenter;positivity
  simp only [extractionQ,show k ≠ 0 by omega,ite_eq_right]
  exact ratioQ_log_scalar _ _ _ _ _ k hM hx hp hh hv hkp

lemma ratioQ_zero_exact (g p : ℕ) : extractionQ g p 0=markedModel g p 0/Real.pi := by
  simp [extractionQ,volume_profile_densityY_zero]

lemma ratioQ_cusp_normalized_log (g p k : ℕ) (hs : Stable g p) (hk : 1 ≤ k) :
    let h : ℝ := complexity g p
    let Y := densityY (2*(k:ℝ)/h)
    let Y' := densityY (2*(k:ℝ)/(h+1))
    Real.log ((extractionQ g (p+1) k/extractionQ g p k)/(h/(A Y*a Y*r Y))) =
      Real.log (h/(h+1))+
        ((Real.log (markedModel g (p+1) Y')-(k:ℝ)*Real.log (XR Y'))-
          (Real.log (markedModel g (p+1) Y)-(k:ℝ)*Real.log (XR Y)))+
        (1/2)*(Real.log (euler Psi (XR Y))-Real.log (euler Psi (XR Y'))) := by
  dsimp only
  have hc : complexity g (p+1)=complexity g p+1 := by
    unfold Stable at hs
    unfold complexity
    omega
  have hs' : Stable g (p+1) := by unfold Stable at *;omega
  have hh : 0 < (complexity g p:ℝ) := by
    exact_mod_cast (show 0 < complexity g p by unfold Stable at hs;unfold complexity;omega)
  have hkp : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hpair := ratioQ_saddle_pair (complexity g p) k hh hkp
  have hy : densityY (2*(k:ℝ)/(complexity g p:ℝ)) ∈ Ico (0:ℝ) y₀ :=
    ⟨hpair.2.1.1.le,hpair.2.1.2⟩
  have hd : 0 < A (densityY (2*(k:ℝ)/(complexity g p:ℝ)))*
      a (densityY (2*(k:ℝ)/(complexity g p:ℝ)))*
      r (densityY (2*(k:ℝ)/(complexity g p:ℝ))) := by
    exact mul_pos (mul_pos (marked_A_pos _ ⟨hy.1,hy.2.le⟩) (a_pos _ hy)) (r_pos _ hy)
  have hlog := ratioQ_model_log_scalar _ _ (complexity g p)
    (A (densityY (2*(k:ℝ)/(complexity g p:ℝ)))*
      a (densityY (2*(k:ℝ)/(complexity g p:ℝ)))*
      r (densityY (2*(k:ℝ)/(complexity g p:ℝ))))
    (markedModel_pos_parameter g p hs _ hy) hh hd
    (by simpa only [Nat.cast_add,Nat.cast_one] using ratioModel_cusp_identity g p hs _ hy)
  rw [Real.log_div (div_pos (ratioQ_pos g (p+1) k hs') (ratioQ_pos g p k hs)).ne'
    (div_pos hh hd).ne',Real.log_div (ratioQ_pos g (p+1) k hs').ne' (ratioQ_pos g p k hs).ne',
    ratioQ_log_exact g (p+1) k hs' hk,ratioQ_log_exact g p k hs hk,hc]
  simp only [Nat.cast_add,Nat.cast_one]
  rw [hlog,Real.log_div hh.ne' (by positivity : (complexity g p:ℝ)+1 ≠ 0)]
  ring

lemma ratioQ_cusp_zero_normalized (g p : ℕ) (hs : Stable g p) :
    (extractionQ g (p+1) 0/extractionQ g p 0)/
      ((complexity g p:ℝ)/(A 0*a 0*r 0)) =
        Real.sqrt ((complexity g p:ℝ)/((complexity g p:ℝ)+1)) := by
  rw [ratioQ_zero_exact,ratioQ_zero_exact,ratioModel_cusp_identity g p hs 0 ⟨le_rfl,y₀_pos⟩]
  have hM := markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩
  have hh : (complexity g p:ℝ) ≠ 0 := by
    exact_mod_cast (show complexity g p ≠ 0 by unfold Stable at hs;unfold complexity;omega)
  have hD : A 0*a 0*r 0 ≠ 0 :=
    (mul_pos (mul_pos (marked_A_pos 0 ⟨le_rfl,y₀_pos.le⟩) (a_pos 0 ⟨le_rfl,y₀_pos⟩))
      (r_pos 0 ⟨le_rfl,y₀_pos⟩)).ne'
  push_cast
  field_simp [hM.ne',hh,hD,Real.pi_ne_zero] <;> simp_all

lemma ratioQ_abs_log_complexity_step (h : ℝ) (hh : 0 < h) :
    |Real.log (h/(h+1))| ≤ 1/h := by
  have hr : 0 < h/(h+1) := by positivity
  have hle : h/(h+1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  rw [abs_of_nonpos (Real.log_nonpos hr.le hle),←Real.log_inv]
  have he : (h/(h+1))⁻¹=(h+1)/h := by field_simp
  rw [he]
  calc
    _ ≤ (h+1)/h-1 := Real.log_le_sub_one_of_pos (by positivity)
    _ = 1/h := by field_simp;ring

lemma ratioQ_cusp_profile_factor (g k : ℕ) (hg : 1 ≤ g) :
    let h : ℝ := complexity g 1
    let Y := densityY (2*(k:ℝ)/h)
    ((2*Real.pi^2)*extractionQ g 2 k/(2*g*extractionQ g 1 k))/profileC (2*(k:ℝ)/h) =
      ((extractionQ g 2 k/extractionQ g 1 k)/(h/(A Y*a Y*r Y)))*(h/(h+1)) := by
  dsimp only
  have hs : Stable g 1 := by unfold Stable;omega
  have hh : 0 < (complexity g 1:ℝ) := by
    exact_mod_cast (show 0 < complexity g 1 by unfold complexity;omega)
  have hcast : (complexity g 1:ℝ)+1=2*(g:ℝ) := by
    have he : complexity g 1+1=2*g := by unfold complexity;omega
    exact_mod_cast he
  have hY := (densityY_spec (2*(k:ℝ)/(complexity g 1:ℝ)) (by positivity)).1
  have hD : 0 < A (densityY (2*(k:ℝ)/(complexity g 1:ℝ)))*
      a (densityY (2*(k:ℝ)/(complexity g 1:ℝ)))*
      r (densityY (2*(k:ℝ)/(complexity g 1:ℝ))) := by
    exact mul_pos (mul_pos (marked_A_pos _ ⟨hY.1,hY.2.le⟩) (a_pos _ hY)) (r_pos _ hY)
  have hQ := ratioQ_pos g 1 k hs
  rw [volume_profile_C_physical _ (by positivity)]
  unfold volumeProfileCPhysical
  rw [J_sub_XR_eq_Aar _ hY,←hcast]
  field_simp [hD.ne',hh.ne',hQ.ne',Real.pi_ne_zero]

lemma ratioQ_cusp_profile_pos (g k : ℕ) (hg : 1 ≤ g) :
    0 < ((2*Real.pi^2)*extractionQ g 2 k/(2*g*extractionQ g 1 k))/
      profileC (2*(k:ℝ)/(complexity g 1:ℝ)) := by
  have hg' : 0 < (g:ℝ) := by exact_mod_cast (show 0 < g by omega)
  have hh : 0 < (complexity g 1:ℝ) := by
    exact_mod_cast (show 0 < complexity g 1 by unfold complexity;omega)
  have hQ := ratioQ_pos g 1 k (by unfold Stable;omega)
  have hQ' := ratioQ_pos g 2 k (by unfold Stable;omega)
  have hprof := volume_profile_C_pos (2*(k:ℝ)/(complexity g 1:ℝ)) (by positivity)
  positivity

lemma ratioQ_cusp_profile_log_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ k : ℕ,
      |Real.log (((2*Real.pi^2)*extractionQ g 2 k/(2*g*extractionQ g 1 k))/
        profileC (2*(k:ℝ)/(complexity g 1:ℝ)))| ≤ C/(complexity g 1:ℝ) := by
  obtain ⟨B,hB,hvariation⟩ := ratioModel_cusp_actual_saddle_log_bounds
  refine ⟨2+2*B,by positivity,?_⟩
  intro g hg k
  have hs : Stable g 1 := by unfold Stable;omega
  have hh : 0 < (complexity g 1:ℝ) := by
    exact_mod_cast (show 0 < complexity g 1 by unfold complexity;omega)
  have hstep := ratioQ_abs_log_complexity_step (complexity g 1) hh
  have hratio : 0 < (complexity g 1:ℝ)/((complexity g 1:ℝ)+1) := by positivity
  rw [ratioQ_cusp_profile_factor g k hg]
  by_cases hk : k = 0
  · subst k
    simp only [Nat.cast_zero,mul_zero,zero_div,volume_profile_densityY_zero]
    rw [ratioQ_cusp_zero_normalized g 1 hs,
      Real.log_mul (Real.sqrt_pos.mpr hratio).ne' hratio.ne',Real.log_sqrt hratio.le]
    calc
      _ = (3/2)*|Real.log ((complexity g 1:ℝ)/((complexity g 1:ℝ)+1))| := by
        rw [show Real.log ((complexity g 1:ℝ)/((complexity g 1:ℝ)+1))/2+
          Real.log ((complexity g 1:ℝ)/((complexity g 1:ℝ)+1)) =
          (3/2)*Real.log ((complexity g 1:ℝ)/((complexity g 1:ℝ)+1)) by ring,
          abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2)]
      _ ≤ (3/2)*(1/(complexity g 1:ℝ)) := mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ ≤ (2+2*B)/(complexity g 1:ℝ) := by
        rw [←mul_div_assoc,mul_one]
        exact div_le_div_of_nonneg_right (by linarith) hh.le
  · have hk1 : 1 ≤ k := by omega
    have hY := (ratioQ_saddle_spec (complexity g 1) k hh (by exact_mod_cast Nat.pos_of_ne_zero hk)).1
    have hD : 0 < A (densityY (2*(k:ℝ)/(complexity g 1:ℝ)))*
        a (densityY (2*(k:ℝ)/(complexity g 1:ℝ)))*
        r (densityY (2*(k:ℝ)/(complexity g 1:ℝ))) := by
      exact mul_pos (mul_pos (marked_A_pos _ ⟨hY.1.le,hY.2.le⟩) (a_pos _ ⟨hY.1.le,hY.2⟩))
        (r_pos _ ⟨hY.1.le,hY.2⟩)
    have hz : 0 < (extractionQ g 2 k/extractionQ g 1 k)/
        ((complexity g 1:ℝ)/(A (densityY (2*(k:ℝ)/(complexity g 1:ℝ)))*
          a (densityY (2*(k:ℝ)/(complexity g 1:ℝ)))*
          r (densityY (2*(k:ℝ)/(complexity g 1:ℝ))))) :=
      div_pos (div_pos (ratioQ_pos g 2 k (by unfold Stable;omega)) (ratioQ_pos g 1 k hs)) (div_pos hh hD)
    rw [Real.log_mul hz.ne' hratio.ne',ratioQ_cusp_normalized_log g 1 k hs hk1]
    have hv := hvariation g k hg hk1
    dsimp only at hv
    let h : ℝ := complexity g 1
    let Y := densityY (2*(k:ℝ)/h)
    let Y' := densityY (2*(k:ℝ)/(h+1))
    let L := Real.log (h/(h+1))
    let T := (Real.log (markedModel g 2 Y')-(k:ℝ)*Real.log (XR Y'))-
      (Real.log (markedModel g 2 Y)-(k:ℝ)*Real.log (XR Y))
    let V := Real.log (euler Psi (XR Y))-Real.log (euler Psi (XR Y'))
    change |(L+T+(1/2)*V)+L| ≤ (2+2*B)/h
    have hL : |L| ≤ 1/h := hstep
    have hT : |T| ≤ B/h := hv.1
    have hV : |V| ≤ B/h := by simpa only [abs_sub_comm] using hv.2
    calc
      _ ≤ (|L|+|T|+(1/2)*|V|)+|L| := by
        have ht := abs_add_le (L+T) ((1/2)*V)
        rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at ht
        nlinarith [abs_add_le L T,abs_add_le (L+T+(1/2)*V) L]
      _ ≤ (1/h+B/h+(1/2)*(B/h))+1/h := by gcongr
      _ = (2+(3/2)*B)/h := by ring
      _ ≤ (2+2*B)/h := div_le_div_of_nonneg_right (by linarith) hh.le

/-- The actual full Q ratio at the two finite-genus saddles, with the
Poisson and variance normalization retained, including k=0. -/
lemma ratioQ_cusp_uniform_rate :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ k : ℕ,
      |((2*Real.pi^2)*extractionQ g 2 k/(2*g*extractionQ g 1 k))/
        profileC (2*(k:ℝ)/(complexity g 1:ℝ))-1| ≤ C/g := by
  obtain ⟨B,hB,hlog⟩ := ratioQ_cusp_profile_log_uniform
  obtain ⟨N,hN⟩ := exists_nat_ge B
  refine ⟨2*B,by positivity,1+N,?_⟩
  intro g hg k
  have hg1 : 1 ≤ g := by omega
  have hgp : 0 < (g:ℝ) := by exact_mod_cast (show 0 < g by omega)
  have hh : (g:ℝ) ≤ (complexity g 1:ℝ) := by
    exact_mod_cast (show g ≤ complexity g 1 by unfold complexity;omega)
  have hsmall : B/(g:ℝ) ≤ 1 := by
    apply (div_le_one hgp).2
    exact hN.trans (by exact_mod_cast (show N ≤ g by omega))
  have hbound := (hlog g hg1 k).trans (div_le_div_of_nonneg_left hB.le hgp hh)
  have hp := ratioQ_cusp_profile_pos g k hg1
  calc
    _ = |Real.exp (Real.log (((2*Real.pi^2)*extractionQ g 2 k/(2*g*extractionQ g 1 k))/
          profileC (2*(k:ℝ)/(complexity g 1:ℝ))))-1| := by rw [Real.exp_log hp]
    _ ≤ 2*|Real.log (((2*Real.pi^2)*extractionQ g 2 k/(2*g*extractionQ g 1 k))/
          profileC (2*(k:ℝ)/(complexity g 1:ℝ)))| :=
      Real.abs_exp_sub_one_le (hbound.trans hsmall)
    _ ≤ 2*(B/g) := mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = (2*B)/g := by ring

end WP.Analysis
