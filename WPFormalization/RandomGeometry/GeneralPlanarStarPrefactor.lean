import WPFormalization.RandomGeometry.PantsFixedOrderAsymptotics
import WPFormalization.RandomGeometry.PrimitivePlanarScale

/-! Fixed general planar-star zero-boundary numerical factor.
The actual all-cusp volume ratios and saddle/profile relation give a relative
factor tending to one. The remaining finite-type moving weight is uniformly
bounded on the compact physical cusp interval, including its zero endpoint.
Thus the absolute asymptotic remains valid when limiting weights vanish. -/
noncomputable section
namespace WP.RandomGeometry
open Filter Set
open scoped Topology

lemma general_planar_saddle_mem (g n : ℕ) (hg : 1 ≤ g) (hn : 2 ≤ n) :
    primitiveSaddleX g n ∈ Ioo (0 : ℝ) xCritical := by
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hnm : 0 < ((n-1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n-1 by omega)
  have hh : 0 < 2*(g:ℝ)-1 := by linarith
  have hs := Analysis.physicalDensitySaddle_spec
    (((n-1 : ℕ) : ℝ)/(2*(g:ℝ)-1)) (div_pos hnm hh)
  have he : XR (densityY (2*(((n-1 : ℕ) : ℝ)/(2*(g:ℝ)-1)))) = primitiveSaddleX g n := by
    unfold primitiveSaddleX
    congr 2
    ring
  rw [he] at hs
  exact hs.1

lemma general_planar_saddle_profile_identity (g n : ℕ) (hg : 1 ≤ g) (hn : 2 ≤ n) :
    (2*g*profileC ((n:ℝ)/g)) * (primitiveSaddleX g n/(2*Real.pi^2*(n:ℝ))) =
      (primitivePlanarEffectiveScale g n/pantsScale g n) * (((n:ℝ)-1)/(n:ℝ)) := by
  have hx := (general_planar_saddle_mem g n hg hn).1.ne'
  have hgR : (0:ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by linarith
  have hn1 : (n:ℝ)-1 ≠ 0 := by linarith
  have hC := (Analysis.volume_profile_C_pos ((n:ℝ)/g) (by positivity)).ne'
  unfold primitivePlanarEffectiveScale pantsScale
  field_simp [hx, hgR.ne', hn0, hn1, hC, Real.pi_ne_zero]
  ring

lemma general_planar_saddle_profile_tendsto_one (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) :
    Tendsto (fun g => (2*g*profileC ((n g:ℝ)/g)) *
      (primitiveSaddleX g (n g)/(2*Real.pi^2*(n g:ℝ)))) atTop (𝓝 1) := by
  have hc := primitive_planar_scale_ratio_tendsto_one n (hn.eventually_ge_atTop 2)
  have hi := (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp hn
  have hh := (tendsto_const_nhds (x := (1:ℝ))).sub hi
  simp only [sub_zero] at hh
  have ht := hc.mul hh
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ), hn.eventually_ge_atTop 2] with g hg hng
  rw [general_planar_saddle_profile_identity g (n g) hg hng]
  have hn0 : (n g:ℝ) ≠ 0 := by exact_mod_cast (show n g ≠ 0 by omega)
  congr 1
  dsimp only [Function.comp_def]
  field_simp

lemma general_planar_fixed_volume_ratio (P : PsiTheory) (d : ℕ)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun g => (2*Real.pi^2*(n g:ℝ)/primitiveSaddleX g (n g))^d *
      volumeModel P g (n g-d)/volumeModel P g (n g)) atTop (𝓝 1) := by
  have ht := (pants_fixed_volume_ratio P d n hn).div
    ((general_planar_saddle_profile_tendsto_one n hn).pow d) (by simp : (1:ℝ)^d ≠ 0)
  simp only [one_pow,div_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ), hn.eventually_ge_atTop 2] with g hg hng
  have hx := (general_planar_saddle_mem g (n g) hg hng).1.ne'
  have hgR : (0:ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hnR : (0:ℝ) < n g := by exact_mod_cast (show 0 < n g by omega)
  have hC := (Analysis.volume_profile_C_pos ((n g:ℝ)/g) (by positivity)).ne'
  change (2*g*profileC ((n g:ℝ)/g))^d * volumeModel P g (n g-d)/volumeModel P g (n g) /
    ((2*g*profileC ((n g:ℝ)/g)) * (primitiveSaddleX g (n g)/(2*Real.pi^2*(n g:ℝ))))^d = _
  simp only [mul_pow,div_pow]
  field_simp [hx,hgR.ne',hnR.ne',hC,Real.pi_ne_zero]

lemma general_planar_prefactor_algebra (N x P V U a w : ℝ) (e r : ℕ)
    (hN : N ≠ 0) (hx : x ≠ 0) (hP : P ≠ 0) (hV : V ≠ 0) (D : ℝ) :
    (D/V*U*a)*(w/(2*(N*x/(4*P)))^r) =
      (D/N^(e+2*r)*((P*N/x)^(e+r)*U/V)) *
        (2^r*a*(x/P)^e*w) := by
  simp only [mul_pow,div_pow,pow_add,pow_mul]
  field_simp
  simp only [show (4 : ℝ) = 2^2 by norm_num, ← pow_mul, Nat.mul_comm 2 r]

def generalPlanarStarBase (P : PsiTheory) (g n r : ℕ) (k : Fin r → ℕ)
    (lo hi : Fin r → ℝ) : ℝ :=
  ((n.descFactorial (∑ i,k i) : ℝ)/volumeModel P g n) *
    volumeModel P g (n-((∑ i,k i)-r)) *
    (∏ i,volumeModel P 0 (k i+1)/((k i).factorial:ℝ)) *
    ∏ i,((hi i)^2-(lo i)^2)/(2*primitivePlanarEffectiveScale g n)

def generalPlanarStarWeight (P : PsiTheory) (r : ℕ) (k : Fin r → ℕ)
    (lo hi : Fin r → ℝ) (x : ℝ) : ℝ :=
  ∏ i,2*volumeModel P 0 (k i+1)/((k i).factorial:ℝ) *
    (x/(2*Real.pi^2))^(k i-2) * ((hi i)^2-(lo i)^2)

def generalPlanarStarRelativeError (P : PsiTheory) (g n r : ℕ) (k : Fin r → ℕ) : ℝ :=
  ((n.descFactorial (∑ i,k i):ℝ)/(n:ℝ)^(∑ i,k i)) *
    ((2*Real.pi^2*(n:ℝ)/primitiveSaddleX g n)^((∑ i,k i)-r) *
      volumeModel P g (n-((∑ i,k i)-r))/volumeModel P g n)

lemma general_planar_star_relative_error (P : PsiTheory) (r : ℕ) (k : Fin r → ℕ)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun g => generalPlanarStarRelativeError P g (n g) r k) atTop (𝓝 1) := by
  simpa only [generalPlanarStarRelativeError,one_mul] using
    (pants_fixed_descFactorial_limit (∑ i,k i) n hn).mul
      (general_planar_fixed_volume_ratio P ((∑ i,k i)-r) n hn)

lemma general_planar_star_weight_product (P : PsiTheory) (r : ℕ) (k : Fin r → ℕ)
    (lo hi : Fin r → ℝ) (x : ℝ) :
    generalPlanarStarWeight P r k lo hi x =
      2^r * (∏ i,volumeModel P 0 (k i+1)/((k i).factorial:ℝ)) *
      (x/(2*Real.pi^2))^(∑ i,(k i-2)) * ∏ i,((hi i)^2-(lo i)^2) := by
  have he (i : Fin r) :
      2*volumeModel P 0 (k i+1)/((k i).factorial:ℝ) =
        2*(volumeModel P 0 (k i+1)/((k i).factorial:ℝ)) := by ring
  simp only [generalPlanarStarWeight,he,Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma general_planar_star_base_identity (P : PsiTheory) (g n r : ℕ) (k : Fin r → ℕ)
    (lo hi : Fin r → ℝ) (hg : 1 ≤ g) (hn : 2 ≤ n) (hk : ∀ i,2 ≤ k i) :
    generalPlanarStarBase P g n r k lo hi = generalPlanarStarRelativeError P g n r k *
      generalPlanarStarWeight P r k lo hi (primitiveSaddleX g n) := by
  let e := ∑ i,(k i-2)
  let K := ∑ i,k i
  have hK : K=e+2*r := by
    calc
      K = ∑ i,(k i-2+2) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Nat.sub_add_cancel (hk i)).symm
      _ = e+2*r := by rw [Finset.sum_add_distrib]; simp [e,mul_comm]
  have hd : K-r=e+r := by omega
  have hx := (general_planar_saddle_mem g n hg hn).1.ne'
  have hN : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hV := (diagonal_volume_pos_nonempty P g n (by omega)
    (by unfold Stable;omega)).ne'
  rw [general_planar_star_weight_product]
  have hw : (∏ i,((hi i)^2-(lo i)^2)/(2*primitivePlanarEffectiveScale g n)) =
      (∏ i,((hi i)^2-(lo i)^2))/(2*primitivePlanarEffectiveScale g n)^r := by
    rw [Finset.prod_div_distrib]
    simp
  unfold generalPlanarStarBase generalPlanarStarRelativeError
  rw [hw]
  change (((n.descFactorial K:ℝ)/volumeModel P g n) * volumeModel P g (n-(K-r)) *
    (∏ i,volumeModel P 0 (k i+1)/((k i).factorial:ℝ))) *
      ((∏ i,((hi i)^2-(lo i)^2))/(2*primitivePlanarEffectiveScale g n)^r) = _
  change (((n.descFactorial K:ℝ)/volumeModel P g n) * volumeModel P g (n-(K-r)) *
    (∏ i,volumeModel P 0 (k i+1)/((k i).factorial:ℝ))) *
      ((∏ i,((hi i)^2-(lo i)^2))/(2*primitivePlanarEffectiveScale g n)^r) =
    ((n.descFactorial K:ℝ)/(n:ℝ)^K *
      ((2*Real.pi^2*(n:ℝ)/primitiveSaddleX g n)^(K-r) *
        volumeModel P g (n-(K-r))/volumeModel P g n)) *
      (2^r*(∏ i,volumeModel P 0 (k i+1)/((k i).factorial:ℝ)) *
        (primitiveSaddleX g n/(2*Real.pi^2))^e * (∏ i,((hi i)^2-(lo i)^2)))
  rw [hd,show (n:ℝ)^K=(n:ℝ)^(e+2*r) by rw [hK]]
  exact general_planar_prefactor_algebra (n:ℝ) (primitiveSaddleX g n)
    (2*Real.pi^2) (volumeModel P g n) (volumeModel P g (n-(e+r)))
    (∏ i,volumeModel P 0 (k i+1)/((k i).factorial:ℝ))
    (∏ i,((hi i)^2-(lo i)^2)) e r hN hx (by positivity) hV (n.descFactorial K:ℝ)

lemma general_planar_star_weight_continuous (P : PsiTheory) (r : ℕ) (k : Fin r → ℕ)
    (lo hi : Fin r → ℝ) : Continuous (generalPlanarStarWeight P r k lo hi) := by
  unfold generalPlanarStarWeight
  fun_prop

lemma general_planar_star_weight_bounded (P : PsiTheory) (r : ℕ) (k : Fin r → ℕ)
    (lo hi : Fin r → ℝ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    IsBoundedUnder (· ≤ ·) atTop (fun g =>
      ‖generalPlanarStarWeight P r k lo hi (primitiveSaddleX g (n g))‖) := by
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) xCritical)).exists_bound_of_continuousOn
    (general_planar_star_weight_continuous P r k lo hi).continuousOn
  apply isBoundedUnder_of_eventually_le (a := M)
  filter_upwards [eventually_ge_atTop (1:ℕ),hn.eventually_ge_atTop 2] with g hg hng
  have hx := general_planar_saddle_mem g (n g) hg hng
  exact hM _ ⟨hx.1.le,hx.2.le⟩

/-- The moving-weight absolute limit includes vanishing limiting weights and
zero-width windows; no density limit or lower bound on a weight is required. -/
theorem general_planar_star_base_asymptotic (P : PsiTheory) (r : ℕ) (k : Fin r → ℕ)
    (lo hi : Fin r → ℝ) (hk : ∀ i,2 ≤ k i)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun g => generalPlanarStarBase P g (n g) r k lo hi -
      generalPlanarStarWeight P r k lo hi (primitiveSaddleX g (n g))) atTop (𝓝 0) := by
  have he := (general_planar_star_relative_error P r k n hn).sub_const 1
  simp only [sub_self] at he
  have ht := he.zero_mul_isBoundedUnder_le (general_planar_star_weight_bounded P r k lo hi n hn)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ),hn.eventually_ge_atTop 2] with g hg hng
  rw [general_planar_star_base_identity P g (n g) r k lo hi hg hng hk]
  ring

/-- The original fast-cusp hypotheses are sufficient, with no bound on n/g. -/
theorem general_planar_star_base_asymptotic_fast (P : PsiTheory) (r : ℕ) (k : Fin r → ℕ)
    (lo hi : Fin r → ℝ) (hk : ∀ i,2 ≤ k i)
    (n : ℕ → ℕ) (hn : Tendsto (fun g:ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop) :
    Tendsto (fun g => generalPlanarStarBase P g (n g) r k lo hi -
      generalPlanarStarWeight P r k lo hi (primitiveSaddleX g (n g))) atTop (𝓝 0) := by
  have hnreal : Tendsto (fun g => (n g:ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hn
    filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
    have hgR : (1:ℝ) ≤ g := by exact_mod_cast hg
    have hs : 1 ≤ Real.sqrt (g:ℝ) :=
      (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
    exact div_le_self (by positivity) hs
  exact general_planar_star_base_asymptotic P r k lo hi hk n
    (tendsto_natCast_atTop_iff.mp hnreal)

lemma general_planar_star_base_zero (P : PsiTheory) (g n : ℕ) (k : Fin 0 → ℕ)
    (lo hi : Fin 0 → ℝ) (hg : 1 ≤ g) (hn : 1 ≤ n) :
    generalPlanarStarBase P g n 0 k lo hi = 1 := by
  have hV := (diagonal_volume_pos_nonempty P g n hn (by unfold Stable;omega)).ne'
  simp [generalPlanarStarBase,hV]

@[simp] lemma general_planar_star_weight_zero (P : PsiTheory) (k : Fin 0 → ℕ)
    (lo hi : Fin 0 → ℝ) (x : ℝ) : generalPlanarStarWeight P 0 k lo hi x = 1 := by
  simp [generalPlanarStarWeight]

end WP.RandomGeometry
