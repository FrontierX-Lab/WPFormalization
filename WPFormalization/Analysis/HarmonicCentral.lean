import WPFormalization.Analysis.HarmonicLocalLimit
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma gaussian_central_lower (L c B v d:ℝ)(hL:0≤L)(hc:0<c)(hB:0<B)(hcv:c≤v)(hvB:v≤B)
    (h:ℕ)(hh:0<h)(hd:|d|≤L*Real.sqrt (h:ℝ)) :
    (Real.exp (-L^2/(2*c))/Real.sqrt (2*Real.pi*B))/Real.sqrt (h:ℝ) ≤
      Real.exp (-d^2/(2*(h:ℝ)*v))/Real.sqrt (2*Real.pi*(h:ℝ)*v) := by
  let r := Real.sqrt (h:ℝ)
  let q := d/r
  have hr : 0<r := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hv : 0<v := lt_of_lt_of_le hc hcv
  have hq : |q|≤L := by dsimp [q]; rw [abs_div,abs_of_pos hr]; exact (div_le_iff₀ hr).mpr hd
  have hq2 : q^2≤L^2 := by nlinarith [sq_abs q,abs_nonneg q]
  have hx : q^2/(2*v)≤L^2/(2*c) :=
    (div_le_div_of_nonneg_right hq2 (by positivity)).trans
      (div_le_div_of_nonneg_left (sq_nonneg L) (by positivity) (by linarith : 2*c≤2*v))
  have he : Real.exp (-L^2/(2*c))≤Real.exp (-q^2/(2*v)) := Real.exp_le_exp.mpr (by
    calc -L^2/(2*c) = -(L^2/(2*c)) := by ring
         _ ≤ -(q^2/(2*v)) := neg_le_neg hx
         _ = -q^2/(2*v) := by ring)
  have hS : Real.sqrt (2*Real.pi*v)≤Real.sqrt (2*Real.pi*B) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
  have hSp : 0<Real.sqrt (2*Real.pi*v) := Real.sqrt_pos.mpr (by positivity)
  have hLow : Real.exp (-L^2/(2*c))/Real.sqrt (2*Real.pi*B)≤Real.exp (-q^2/(2*v))/Real.sqrt (2*Real.pi*v) :=
    (div_le_div_of_nonneg_right he (Real.sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left (Real.exp_pos _).le hSp hS)
  apply (div_le_iff₀ hr).mpr
  have heScale := gaussian_mass_scaling v d hv h hh
  nlinarith
lemma harmonicSumMass_central_lower (L:ℝ)(hL:0≤L) : ∃c:ℝ,0<c ∧ ∃h₀:ℕ,∀h≥h₀,0<h→
    ∀Y∈Icc (0:ℝ) y₀,∀m:ℕ,|(m:ℝ)-3*(h:ℝ)/2|≤L*Real.sqrt (h:ℝ) →
      c/Real.sqrt (h:ℝ)≤harmonicSumMass Y h m := by
  obtain ⟨c,B,s,hc,hB,hs,hbound⟩ := harmonic_uniform_bounds
  let κ := Real.exp (-L^2/(2*c))/Real.sqrt (2*Real.pi*B)
  have hκ : 0<κ := by dsimp [κ]; positivity
  obtain ⟨h₀,hAfter⟩ := harmonic_local_limit L hL (κ/2) (by positivity)
  refine ⟨κ/2,by positivity,h₀,?_⟩
  intro h hhh hh Y hY m hm
  have hNear := hAfter h hhh hh Y hY m hm
  have hLow := gaussian_central_lower L c B (harmonicVariance Y) ((m:ℝ)-3*(h:ℝ)/2) hL hc hB
    (hbound Y hY).2.2.1 (hbound Y hY).2.2.2.1 h hh hm
  have hAbs := (abs_le.mp hNear).1
  calc (κ/2)/Real.sqrt (h:ℝ) = κ/Real.sqrt (h:ℝ)-(κ/2)/Real.sqrt (h:ℝ) := by ring
       _ ≤ _ := sub_le_sub_right hLow _
       _ ≤ harmonicSumMass Y h m := by linarith
lemma harmonicSumMass_eq_normalized_coeff (Y:ℝ)(hY:Y∈Icc 0 y₀)(h m:ℕ) :
    harmonicSumMass Y h m=(barH Y 1).re^h*harmonicCoeff Y h m := by
  have he : (fun w=>harmonicPGF Y w^h) = fun w=>(((barH Y 1).re^h:ℝ):ℂ)*(barH Y w)⁻¹^h := by
    rw [harmonicPGF_eq_real_mul_inv]
    funext w
    simp only [mul_pow,Complex.ofReal_pow]
  unfold harmonicSumMass harmonicCoeff
  rw [he,realCoeff_const_mul]
lemma harmonicCoeff_central_lower (L:ℝ)(hL:0≤L) : ∃c:ℝ,0<c ∧ ∃h₀:ℕ,∀h≥h₀,0<h→
    ∀Y∈Icc (0:ℝ) y₀,∀m:ℕ,|(m:ℝ)-3*(h:ℝ)/2|≤L*Real.sqrt (h:ℝ) →
      c/(Real.sqrt (h:ℝ)*(barH Y 1).re^h)≤harmonicCoeff Y h m := by
  obtain ⟨c,hc,h₀,hAfter⟩ := harmonicSumMass_central_lower L hL
  refine ⟨c,hc,h₀,?_⟩
  intro h hhh hh Y hY m hm
  have hp : 0<(barH Y 1).re^h := pow_pos (barH_one_re_pos Y hY) h
  have hLow := hAfter h hhh hh Y hY m hm
  rw [harmonicSumMass_eq_normalized_coeff Y hY h m] at hLow
  rw [show c/(Real.sqrt (h:ℝ)*(barH Y 1).re^h)=(c/Real.sqrt (h:ℝ))/(barH Y 1).re^h by ring]
  apply (div_le_iff₀ hp).mpr
  nlinarith
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma gaussian_mass_upper (c v d:ℝ)(hc:0<c)(hcv:c≤v)(h:ℕ)(hh:0<h) :
    Real.exp (-d^2/(2*(h:ℝ)*v))/Real.sqrt (2*Real.pi*(h:ℝ)*v) ≤
      (1/Real.sqrt (2*Real.pi*c))/Real.sqrt (h:ℝ) := by
  let r := Real.sqrt (h:ℝ)
  let q := d/r
  have hr : 0<r := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hv : 0<v := lt_of_lt_of_le hc hcv
  have hE : Real.exp (-q^2/(2*v))≤1 := by
    apply Real.exp_le_one_iff.mpr
    calc -q^2/(2*v) = -(q^2/(2*v)) := by ring
         _ ≤ 0 := neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by positivity))
  have hS : Real.sqrt (2*Real.pi*c)≤Real.sqrt (2*Real.pi*v) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
  have hSP : 0<Real.sqrt (2*Real.pi*c) := Real.sqrt_pos.mpr (by positivity)
  have hRaw : Real.exp (-q^2/(2*v))/Real.sqrt (2*Real.pi*v)≤1/Real.sqrt (2*Real.pi*c) :=
    (div_le_div_of_nonneg_right hE (Real.sqrt_nonneg _)).trans (div_le_div_of_nonneg_left zero_le_one hSP hS)
  apply (le_div_iff₀ hr).mpr
  have hScale := gaussian_mass_scaling v d hv h hh
  nlinarith
lemma harmonicSumMass_central_upper (L:ℝ)(hL:0≤L) : ∃C:ℝ,0<C ∧ ∃h₀:ℕ,∀h≥h₀,0<h→
    ∀Y∈Icc (0:ℝ) y₀,∀m:ℕ,|(m:ℝ)-3*(h:ℝ)/2|≤L*Real.sqrt (h:ℝ) →
      harmonicSumMass Y h m≤C/Real.sqrt (h:ℝ) := by
  obtain ⟨c,B,s,hc,hB,hs,hbound⟩ := harmonic_uniform_bounds
  let C := 1/Real.sqrt (2*Real.pi*c)+1
  have hC : 0<C := by dsimp [C]; positivity
  obtain ⟨h₀,hAfter⟩ := harmonic_local_limit L hL 1 zero_lt_one
  refine ⟨C,hC,h₀,?_⟩
  intro h hhh hh Y hY m hm
  have hNear := hAfter h hhh hh Y hY m hm
  have hUpper := gaussian_mass_upper c (harmonicVariance Y) ((m:ℝ)-3*(h:ℝ)/2) hc (hbound Y hY).2.2.1 h hh
  have hAbs := (abs_le.mp hNear).2
  calc harmonicSumMass Y h m ≤ Real.exp (-((m:ℝ)-3*(h:ℝ)/2)^2/(2*(h:ℝ)*harmonicVariance Y))/Real.sqrt (2*Real.pi*(h:ℝ)*harmonicVariance Y)+1/Real.sqrt (h:ℝ) := by linarith
       _ ≤ (1/Real.sqrt (2*Real.pi*c))/Real.sqrt (h:ℝ)+1/Real.sqrt (h:ℝ) := by linarith [hUpper]
       _ = C/Real.sqrt (h:ℝ) := by dsimp [C]; ring
lemma harmonicSumMass_central_log_bound (L:ℝ)(hL:0≤L) : ∃C:ℝ,0<C ∧ ∃h₀:ℕ,∀h≥h₀,0<h→
    ∀Y∈Icc (0:ℝ) y₀,∀m:ℕ,|(m:ℝ)-3*(h:ℝ)/2|≤L*Real.sqrt (h:ℝ) →
      |Real.log (harmonicSumMass Y h m)+Real.log (h:ℝ)/2|≤C := by
  obtain ⟨c,hc,h₀,hLower⟩ := harmonicSumMass_central_lower L hL
  obtain ⟨B,hB,h₁,hUpper⟩ := harmonicSumMass_central_upper L hL
  let C := |Real.log c|+|Real.log B|+1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,max h₀ h₁,?_⟩
  intro h hhh hh Y hY m hm
  have hr : 0<Real.sqrt (h:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hl := hLower h ((le_max_left _ _).trans hhh) hh Y hY m hm
  have hu := hUpper h ((le_max_right _ _).trans hhh) hh Y hY m hm
  have hp : 0<harmonicSumMass Y h m := lt_of_lt_of_le (div_pos hc hr) hl
  have hlp : c≤Real.sqrt (h:ℝ)*harmonicSumMass Y h m := by nlinarith [(div_le_iff₀ hr).mp hl]
  have hup : Real.sqrt (h:ℝ)*harmonicSumMass Y h m≤B := by nlinarith [(le_div_iff₀ hr).mp hu]
  have hlogL := Real.log_le_log hc hlp
  have hlogU := Real.log_le_log (mul_pos hr hp) hup
  have hlog : |Real.log (Real.sqrt (h:ℝ)*harmonicSumMass Y h m)|≤C := by
    apply abs_le.mpr
    dsimp [C]
    constructor
    · linarith [neg_abs_le (Real.log c),abs_nonneg (Real.log B)]
    · linarith [le_abs_self (Real.log B),abs_nonneg (Real.log c)]
  rw [Real.log_mul (ne_of_gt hr) (ne_of_gt hp),Real.log_sqrt (by positivity : (0:ℝ)≤h)] at hlog
  simpa only [add_comm] using hlog
lemma harmonicCoeff_central_log_bound (L:ℝ)(hL:0≤L) : ∃C:ℝ,0<C ∧ ∃h₀:ℕ,∀h≥h₀,0<h→
    ∀Y∈Icc (0:ℝ) y₀,∀m:ℕ,|(m:ℝ)-3*(h:ℝ)/2|≤L*Real.sqrt (h:ℝ) →
      |Real.log (harmonicCoeff Y h m)+(h:ℝ)*Real.log (barH Y 1).re+Real.log (h:ℝ)/2|≤C := by
  obtain ⟨C,hC,h₀,hAfter⟩ := harmonicSumMass_central_log_bound L hL
  refine ⟨C,hC,h₀,?_⟩
  intro h hhh hh Y hY m hm
  have hlog := hAfter h hhh hh Y hY m hm
  have hp := pow_pos (barH_one_re_pos Y hY) h
  have hCoeff := harmonicCoeff_pos Y h m hh hY
  rw [harmonicSumMass_eq_normalized_coeff Y hY h m,Real.log_mul (ne_of_gt hp) (ne_of_gt hCoeff),Real.log_pow] at hlog
  simpa only [add_comm,add_left_comm,add_assoc] using hlog
end WP.Analysis
