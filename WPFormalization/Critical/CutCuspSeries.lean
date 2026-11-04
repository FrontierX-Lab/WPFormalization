import Mathlib

/-! Actual Appendix G cusp-allocation series. All estimates concern finite
nonnegative coefficient sums, with exact Gamma coefficients for the two
unstable vertex types and the marked three-cusp replacement. -/

noncomputable section
namespace WP.Critical
open Finset

/-- The actual genus-zero, one-boundary cusp-allocation series in (G.1). -/
def cutPhi01 : PowerSeries ℝ := PowerSeries.mk fun q =>
  if 2 ≤ q then 1 / ((q : ℝ) * ((q : ℝ)-1)) else 0

/-- The actual genus-zero, two-boundary cusp-allocation series in (G.1). -/
def cutPhi02 : PowerSeries ℝ := PowerSeries.mk fun q =>
  if 1 ≤ q then 1 / (q : ℝ) else 0

/-- A specified one-boundary component receiving at least three cusps. -/
def cutPhi01Three : PowerSeries ℝ := PowerSeries.mk fun q =>
  if 3 ≤ q then 1 / ((q : ℝ) * ((q : ℝ)-1)) else 0

def cutCoefficientMass (N : ℕ) (f : PowerSeries ℝ) (z : ℝ) : ℝ :=
  ∑ m ∈ range (N+1), PowerSeries.coeff m f * z^m

lemma cutCoefficientMass_nonneg (N : ℕ) (f : PowerSeries ℝ) (z : ℝ)
    (hf : ∀m, 0 ≤ PowerSeries.coeff m f) (hz : 0 ≤ z) :
    0 ≤ cutCoefficientMass N f z :=
  sum_nonneg (fun m _ => mul_nonneg (hf m) (pow_nonneg hz m))

lemma cutCoefficientMass_one (N : ℕ) (z : ℝ) : cutCoefficientMass N 1 z=1 := by
  simp [cutCoefficientMass, PowerSeries.coeff_one]

lemma cutCoefficientMass_mul_le (N : ℕ) (f g : PowerSeries ℝ) (z : ℝ)
    (hf : ∀m, 0 ≤ PowerSeries.coeff m f) (hg : ∀m, 0 ≤ PowerSeries.coeff m g)
    (hz : 0 ≤ z) :
    cutCoefficientMass N (f*g) z ≤ cutCoefficientMass N f z*cutCoefficientMass N g z := by
  have he : cutCoefficientMass N (f*g) z =
      ∑m∈range (N+1), ∑j∈range (m+1),
        (PowerSeries.coeff j f*z^j)*(PowerSeries.coeff (m-j) g*z^(m-j)) := by
    unfold cutCoefficientMass
    apply sum_congr rfl
    intro m hm
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      sum_mul]
    apply sum_congr rfl
    intro j hj
    have hjm : j ≤ m := by have := mem_range.mp hj; omega
    have hzexp : z^m = z^j*z^(m-j) := by rw [←pow_add,Nat.add_sub_of_le hjm]
    rw [hzexp]
    ring
  rw [he, sum_range_diag_flip (N+1) (fun i j =>
    (PowerSeries.coeff i f*z^i)*(PowerSeries.coeff j g*z^j))]
  unfold cutCoefficientMass
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  rw [mul_sum]
  apply sum_le_sum_of_subset_of_nonneg
  · exact range_mono (Nat.sub_le _ _)
  · intro j hj hnot
    exact mul_nonneg (mul_nonneg (hf i) (pow_nonneg hz i))
      (mul_nonneg (hg j) (pow_nonneg hz j))

lemma cutSeries_mul_nonneg (f g : PowerSeries ℝ)
    (hf : ∀m,0≤PowerSeries.coeff m f) (hg : ∀m,0≤PowerSeries.coeff m g) :
    ∀m,0≤PowerSeries.coeff m (f*g) := by
  intro m
  rw [PowerSeries.coeff_mul]
  exact sum_nonneg (fun p _=>mul_nonneg (hf p.1) (hg p.2))

lemma cutSeries_pow_nonneg (f : PowerSeries ℝ)
    (hf : ∀m,0≤PowerSeries.coeff m f) (u : ℕ) :
    ∀m,0≤PowerSeries.coeff m (f^u) := by
  induction u with
  | zero => intro m; simp only [pow_zero,PowerSeries.coeff_one];split_ifs <;>norm_num
  | succ u ih => rw [pow_succ];exact cutSeries_mul_nonneg _ _ ih hf

lemma cutCoefficientMass_pow_le (N : ℕ) (f : PowerSeries ℝ) (z : ℝ)
    (hf : ∀m,0≤PowerSeries.coeff m f) (hz : 0≤z) (u : ℕ) :
    cutCoefficientMass N (f^u) z ≤ (cutCoefficientMass N f z)^u := by
  induction u with
  | zero => simp [cutCoefficientMass_one]
  | succ u ih =>
    rw [pow_succ,pow_succ]
    exact (cutCoefficientMass_mul_le N _ _ z (cutSeries_pow_nonneg f hf u) hf hz).trans
      (mul_le_mul_of_nonneg_right ih (cutCoefficientMass_nonneg N f z hf hz))

lemma cutCoefficientMass_tail_le (N r : ℕ) (f : PowerSeries ℝ) (z : ℝ)
    (hz : 0≤z) (hz' : z≤1/2)
    (hf0 : ∀m,m<r→PowerSeries.coeff m f=0)
    (hf : ∀m,0≤PowerSeries.coeff m f ∧ PowerSeries.coeff m f≤1) :
    cutCoefficientMass N f z ≤ 2*z^r := by
  have hmajor : cutCoefficientMass N f z ≤
      ∑m∈range (r+(N+1)),PowerSeries.coeff m f*z^m := by
    apply sum_le_sum_of_subset_of_nonneg
    · exact range_mono (by omega)
    · intro m hm hnot
      exact mul_nonneg (hf m).1 (pow_nonneg hz m)
  have he : (∑m∈range (r+(N+1)),PowerSeries.coeff m f*z^m) =
      ∑j∈range (N+1),PowerSeries.coeff (r+j) f*z^(r+j) := by
    rw [sum_range_add]
    have hzero : (∑m∈range r,PowerSeries.coeff m f*z^m)=0 := by
      apply sum_eq_zero
      intro m hm
      rw [hf0 m (mem_range.mp hm),zero_mul]
    rw [hzero,zero_add]
  have hg : (∑j∈range (N+1),z^j) ≤ 2 := by
    calc
      _ ≤ ∑j∈range (N+1),(1/2:ℝ)^j :=
        sum_le_sum (fun j _=>pow_le_pow_left₀ hz hz' j)
      _ ≤ ∑'j:ℕ,(1/2:ℝ)^j :=
        Summable.sum_le_tsum (range (N+1)) (fun j _=>by positivity)
          (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      _ = 2 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)];norm_num
  calc
    _ ≤ ∑j∈range (N+1),PowerSeries.coeff (r+j) f*z^(r+j) := hmajor.trans_eq he
    _ ≤ ∑j∈range (N+1),z^(r+j) := sum_le_sum (fun j _=>by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hf (r+j)).2
        (pow_nonneg hz (r+j)))
    _ = z^r*(∑j∈range (N+1),z^j) := by simp only [pow_add,mul_sum]
    _ ≤ z^r*2 := mul_le_mul_of_nonneg_left hg (pow_nonneg hz r)
    _ = 2*z^r := by ring

lemma cutPhi01_coeff_bounds (m : ℕ) :
    0 ≤ PowerSeries.coeff m cutPhi01 ∧ PowerSeries.coeff m cutPhi01 ≤ 1 := by
  simp only [cutPhi01, PowerSeries.coeff_mk]
  split_ifs with hm
  · have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
    have hd : 0 < (m:ℝ)*((m:ℝ)-1) := by nlinarith
    exact ⟨(div_pos (by norm_num) hd).le, (div_le_one₀ hd).mpr (by nlinarith)⟩
  · norm_num

lemma cutPhi02_coeff_bounds (m : ℕ) :
    0 ≤ PowerSeries.coeff m cutPhi02 ∧ PowerSeries.coeff m cutPhi02 ≤ 1 := by
  simp only [cutPhi02, PowerSeries.coeff_mk]
  split_ifs with hm
  · have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
    exact ⟨by positivity, (div_le_one₀ (by linarith)).mpr hmR⟩
  · norm_num

lemma cutPhi01Three_coeff_bounds (m : ℕ) :
    0 ≤ PowerSeries.coeff m cutPhi01Three ∧ PowerSeries.coeff m cutPhi01Three ≤ 1 := by
  simp only [cutPhi01Three, PowerSeries.coeff_mk]
  split_ifs with hm
  · have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
    have hd : 0 < (m:ℝ)*((m:ℝ)-1) := by nlinarith
    exact ⟨(div_pos (by norm_num) hd).le, (div_le_one₀ hd).mpr (by nlinarith)⟩
  · norm_num

lemma cutPhi01_mass_bound (N : ℕ) (z : ℝ) (hz : 0≤z) (hz' : z≤1/2) :
    cutCoefficientMass N cutPhi01 z ≤ 2*z^2 := by
  apply cutCoefficientMass_tail_le N 2 cutPhi01 z hz hz'
  · intro m hm
    simp only [cutPhi01,PowerSeries.coeff_mk,show ¬ 2 ≤ m by omega,ite_false]
  · exact cutPhi01_coeff_bounds

lemma cutPhi02_mass_bound (N : ℕ) (z : ℝ) (hz : 0≤z) (hz' : z≤1/2) :
    cutCoefficientMass N cutPhi02 z ≤ 2*z := by
  simpa only [pow_one] using cutCoefficientMass_tail_le N 1 cutPhi02 z hz hz'
    (fun m hm=>by simp [cutPhi02,show ¬ 1 ≤ m by omega]) cutPhi02_coeff_bounds

lemma cutPhi01Three_mass_bound (N : ℕ) (z : ℝ) (hz : 0≤z) (hz' : z≤1/2) :
    cutCoefficientMass N cutPhi01Three z ≤ 2*z^3 := by
  apply cutCoefficientMass_tail_le N 3 cutPhi01Three z hz hz'
  · intro m hm
    simp only [cutPhi01Three,PowerSeries.coeff_mk,show ¬ 3 ≤ m by omega,ite_false]
  · exact cutPhi01Three_coeff_bounds

/-- The coefficients a_m in Appendix G are fixed by these actual series. -/
def cutCuspAllocationSeries (u v : ℕ) : PowerSeries ℝ := cutPhi01^u*cutPhi02^v

def cutMarkedCuspAllocationSeries (u v : ℕ) : PowerSeries ℝ :=
  cutPhi01Three*cutPhi01^(u-1)*cutPhi02^v

lemma cutCuspAllocation_coeff_nonneg (u v m : ℕ) :
    0 ≤ PowerSeries.coeff m (cutCuspAllocationSeries u v) :=
  cutSeries_mul_nonneg _ _
    (cutSeries_pow_nonneg _ (fun j=>(cutPhi01_coeff_bounds j).1) u)
    (cutSeries_pow_nonneg _ (fun j=>(cutPhi02_coeff_bounds j).1) v) m

lemma cutCuspAllocation_mass_bound (u v N : ℕ) (z : ℝ) (hz : 0≤z) (hz' : z≤1/2) :
    cutCoefficientMass N (cutCuspAllocationSeries u v) z ≤ (2*z^2)^u*(2*z)^v := by
  have h01 : ∀m,0≤PowerSeries.coeff m cutPhi01 := fun m=>(cutPhi01_coeff_bounds m).1
  have h02 : ∀m,0≤PowerSeries.coeff m cutPhi02 := fun m=>(cutPhi02_coeff_bounds m).1
  have h01mass := cutCoefficientMass_nonneg N cutPhi01 z h01 hz
  have h02mass := cutCoefficientMass_nonneg N cutPhi02 z h02 hz
  refine (cutCoefficientMass_mul_le N _ _ z
    (cutSeries_pow_nonneg _ h01 u) (cutSeries_pow_nonneg _ h02 v) hz).trans ?_
  exact mul_le_mul
    ((cutCoefficientMass_pow_le N cutPhi01 z h01 hz u).trans
      (pow_le_pow_left₀ h01mass (cutPhi01_mass_bound N z hz hz') u))
    ((cutCoefficientMass_pow_le N cutPhi02 z h02 hz v).trans
      (pow_le_pow_left₀ h02mass (cutPhi02_mass_bound N z hz hz') v))
    (cutCoefficientMass_nonneg N _ z (cutSeries_pow_nonneg _ h02 v) hz)
    (by positivity)

lemma cutMarkedCuspAllocation_coeff_nonneg (u v m : ℕ) :
    0 ≤ PowerSeries.coeff m (cutMarkedCuspAllocationSeries u v) :=
  cutSeries_mul_nonneg _ _
    (cutSeries_mul_nonneg _ _ (fun j=>(cutPhi01Three_coeff_bounds j).1)
      (cutSeries_pow_nonneg _ (fun j=>(cutPhi01_coeff_bounds j).1) (u-1)))
    (cutSeries_pow_nonneg _ (fun j=>(cutPhi02_coeff_bounds j).1) v) m

lemma cutMarkedCuspAllocation_mass_bound (u v N : ℕ) (z : ℝ) (hz : 0≤z) (hz' : z≤1/2) :
    cutCoefficientMass N (cutMarkedCuspAllocationSeries u v) z ≤
      (2*z^3)*(2*z^2)^(u-1)*(2*z)^v := by
  have h3 : ∀m,0≤PowerSeries.coeff m cutPhi01Three := fun m=>(cutPhi01Three_coeff_bounds m).1
  have h01 : ∀m,0≤PowerSeries.coeff m cutPhi01 := fun m=>(cutPhi01_coeff_bounds m).1
  have h02 : ∀m,0≤PowerSeries.coeff m cutPhi02 := fun m=>(cutPhi02_coeff_bounds m).1
  have h03 := cutSeries_mul_nonneg _ _ h3 (cutSeries_pow_nonneg _ h01 (u-1))
  have hA : cutCoefficientMass N (cutPhi01Three*cutPhi01^(u-1)) z ≤
      (2*z^3)*(2*z^2)^(u-1) := by
    refine (cutCoefficientMass_mul_le N _ _ z h3 (cutSeries_pow_nonneg _ h01 (u-1)) hz).trans ?_
    exact mul_le_mul (cutPhi01Three_mass_bound N z hz hz')
      ((cutCoefficientMass_pow_le N _ z h01 hz (u-1)).trans
        (pow_le_pow_left₀ (cutCoefficientMass_nonneg N _ z h01 hz)
          (cutPhi01_mass_bound N z hz hz') (u-1)))
      (cutCoefficientMass_nonneg N _ z (cutSeries_pow_nonneg _ h01 (u-1)) hz) (by positivity)
  refine (cutCoefficientMass_mul_le N _ _ z h03 (cutSeries_pow_nonneg _ h02 v) hz).trans ?_
  exact mul_le_mul hA
    ((cutCoefficientMass_pow_le N _ z h02 hz v).trans
      (pow_le_pow_left₀ (cutCoefficientMass_nonneg N _ z h02 hz)
        (cutPhi02_mass_bound N z hz hz') v))
    (cutCoefficientMass_nonneg N _ z (cutSeries_pow_nonneg _ h02 v) hz) (by positivity)

end WP.Critical
namespace WP.Critical

lemma cutPhi01Three_eq_sub_leading :
    cutPhi01Three = cutPhi01-PowerSeries.monomial 2 (1/2:ℝ) := by
  ext m
  simp only [map_sub,cutPhi01Three,cutPhi01,PowerSeries.coeff_mk,
    PowerSeries.coeff_monomial]
  by_cases hm : m=2
  · subst m;norm_num
  · have hm' : 2≠m := Ne.symm hm
    rw [if_neg hm]
    by_cases h2 : 2 ≤ m
    · have h3 : 3 ≤ m := by omega
      simp only [h2,h3,ite_true,sub_zero]
    · have h3 : ¬ 3  ≤  m := by omega
      simp only [h2,h3,ite_false,sub_zero]

lemma cutPhi01_coeff_gamma (q : ℕ) (hq : 2 ≤ q) :
    PowerSeries.coeff q cutPhi01=Real.Gamma ((q:ℝ)-1)/(q.factorial:ℝ) := by
  obtain ⟨t,rfl⟩ : ∃t:ℕ,q=t+2 := ⟨q-2,by omega⟩
  rw [cutPhi01,PowerSeries.coeff_mk,if_pos (by omega)]
  rw [show ((t+2:ℕ):ℝ)-1=(t:ℝ)+1 by push_cast;ring,Real.Gamma_nat_eq_factorial]
  have ht : (t.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero t
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  field_simp
  <;>ring

lemma cutPhi02_coeff_gamma (q : ℕ) (hq : 1 ≤ q) :
    PowerSeries.coeff q cutPhi02=Real.Gamma (q:ℝ)/(q.factorial:ℝ) := by
  obtain ⟨t,rfl⟩ : ∃t:ℕ,q=t+1 := ⟨q-1,by omega⟩
  rw [cutPhi02,PowerSeries.coeff_mk,if_pos (by omega),Nat.cast_add,Nat.cast_one,
    Real.Gamma_nat_eq_factorial]
  have ht : (t.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero t
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp
  <;>ring

end WP.Critical
namespace WP.Critical

lemma cutMarkedCuspAllocation_mass_gain (u v N : ℕ) (hu : 1≤u)
    (z : ℝ) (hz : 0≤z) (hz' : z≤1/2) :
    cutCoefficientMass N (cutMarkedCuspAllocationSeries u v) z ≤
      z*((2*z^2)^u*(2*z)^v) := by
  have hp : (2*z^2)^u=(2*z^2)^(u-1)*(2*z^2) := by
    conv_lhs => rw [show u=(u-1)+1 by omega]
    rw [pow_succ]
  refine (cutMarkedCuspAllocation_mass_bound u v N z hz hz').trans_eq ?_
  rw [hp]
  ring

end WP.Critical
