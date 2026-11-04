import WPFormalization.Critical.SurvivingMixedVolumeRatios

/-! The exact ordered cusp-label and side-flip prefactor in (G.6).
There are no factorial-order symmetry factors beyond 2^(r+k). -/
noncomputable section
namespace WP.Critical
open Filter Set
open scoped Topology

/-- The actual volume coefficient in (G.6), including ordered cusp labels. -/
def survivingMixedPrefactor (P : PsiTheory) (g n r k : ℕ) : ℝ :=
  (n.descFactorial (2*r):ℝ)/(2:ℝ)^(r+k) *
    (volumeModel P (g-k) (n-r+2*k)/volumeModel P g n)

lemma surviving_critical_label_scale (n : ℕ → ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g:ℕ => (n g:ℝ)/Real.sqrt g) atTop (𝓝 c)) (r : ℕ) :
    Tendsto (fun g:ℕ => ((n g).descFactorial (2*r):ℝ)/(g:ℝ)^r) atTop (𝓝 (c^(2*r))) := by
  have hnTop := surviving_critical_cusps_tendsto n c hc hn
  have ht := (RandomGeometry.pants_fixed_descFactorial_limit (2*r) n hnTop).mul (hn.pow (2*r))
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [hnTop.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)] with g hng hg
  have hn0 : (n g:ℝ) ≠ 0 := by exact_mod_cast (show n g ≠ 0 by omega)
  have hs : (Real.sqrt (g:ℝ))^(2*r)=(g:ℝ)^r := by
    rw [pow_mul,Real.sq_sqrt (by positivity)]
  rw [div_pow,hs]
  exact div_mul_div_cancel₀ (pow_ne_zero _ hn0)

/-- The exact ordered prefactor tends to the product of the two canonical
intensity constants. No hypothesis relates n/g beyond the critical regime. -/
lemma surviving_mixed_prefactor_tendsto (P : PsiTheory) (n : ℕ → ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g:ℕ => (n g:ℝ)/Real.sqrt g) atTop (𝓝 c)) (r k : ℕ) :
    Tendsto (fun g => survivingMixedPrefactor P g (n g) r k) atTop
      (𝓝 ((c^2/(16*Real.pi^2))^r * (1/2:ℝ)^k)) := by
  have hnTop := surviving_critical_cusps_tendsto n c hc hn
  have hd := surviving_critical_density n c hn
  have ht := ((surviving_critical_label_scale n c hc hn r).mul
    (surviving_mixed_volume_ratio P n hnTop hd r k)).div_const
      ((2:ℝ)^(r+k)*(8*Real.pi^2)^r)
  simp only [mul_one] at ht
  have hconst : c^(2*r)/((2:ℝ)^(r+k)*(8*Real.pi^2)^r)=
      (c^2/(16*Real.pi^2))^r*(1/2:ℝ)^k := by
    rw [pow_add,pow_mul,div_pow,div_pow]
    field_simp
    simp only [mul_pow]
    rw [show (16:ℝ)^r=(2:ℝ)^r*8^r by rw [←mul_pow];norm_num]
    ring
  rw [hconst] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
  have hg0 : (g:ℝ) ≠ 0 := by exact_mod_cast (show g≠0 by omega)
  dsimp [survivingMixedPrefactor]
  rw [mul_pow]
  field_simp

end WP.Critical
