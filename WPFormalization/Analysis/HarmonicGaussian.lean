import WPFormalization.Analysis.HarmonicTaylor
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma variance_quadratic_small (v B t:ℝ)(hv:0≤v)(hvB:v≤B)(ht1:|t|≤1)(htB:B*|t|≤1) :
    v*t^2/2≤1 := by
  have ha : v*|t|≤1 := (mul_le_mul_of_nonneg_right hvB (abs_nonneg t)).trans htB
  have hb := mul_le_mul_of_nonneg_right ha (abs_nonneg t)
  rw [mul_assoc,←sq, sq_abs] at hb
  linarith
lemma real_gaussian_quadratic_error (v B t:ℝ)(hv:0≤v)(hvB:v≤B)(hB:0<B)
    (ht1:|t|≤1)(htB:B*|t|≤1) :
    ‖Complex.exp (-(v:ℂ)/2*(t:ℂ)^2)-(1-(v:ℂ)/2*(t:ℂ)^2)‖≤(B^2/4)*|t|^3 := by
  let x : ℂ := -(v:ℂ)/2*(t:ℂ)^2
  have hxn : ‖x‖=v/2*|t|^2 := by
    dsimp [x]
    simp only [norm_mul,norm_div,norm_neg,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hv,norm_ofNat]
  have hx : ‖x‖≤1 := by
    rw [hxn,sq_abs]
    nlinarith [variance_quadratic_small v B t hv hvB ht1 htB]
  have hb := Complex.norm_exp_sub_one_sub_id_le hx
  have h4 : |t|^4≤|t|^3 := by
    calc |t|^4=|t|^3*|t| := by ring
         _ ≤ |t|^3*1 := mul_le_mul_of_nonneg_left ht1 (by positivity)
         _ = |t|^3 := mul_one _
  have hxx : ‖x‖^2≤(B^2/4)*|t|^3 := by
    calc ‖x‖^2 = (v^2/4)*|t|^4 := by rw [hxn]; ring
         _ ≤ (B^2/4)*|t|^4 := by gcongr
         _ ≤ (B^2/4)*|t|^3 := mul_le_mul_of_nonneg_left h4 (by positivity)
  have he : Complex.exp x-(1-(v:ℂ)/2*(t:ℂ)^2)=Complex.exp x-1-x := by dsimp [x]; ring
  change ‖Complex.exp x-(1-(v:ℂ)/2*(t:ℂ)^2)‖≤_
  rw [he]
  exact hb.trans hxx
lemma centeredHarmonic_uniform_gaussian_error : ∃δ C:ℝ,0<δ ∧ 0<C ∧ ∀Y∈Icc (0:ℝ) y₀,∀t:ℝ,|t|≤δ →
    ‖centeredHarmonic Y t-Complex.exp (-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2)‖≤C*|t|^3 := by
  obtain ⟨δ₀,A,hδ₀,hA,hcubic⟩ := centeredHarmonic_uniform_cubic
  obtain ⟨c,B,s,hc,hB,hs,hbound⟩ := harmonic_uniform_bounds
  let δ := min δ₀ (min 1 (1/B))
  have hδ : 0<δ := by dsimp [δ]; positivity
  refine ⟨δ,A+B^2/4,hδ,by positivity,?_⟩
  intro Y hY t ht
  have hv0 : 0≤harmonicVariance Y := (lt_of_lt_of_le hc (hbound Y hY).2.2.1).le
  have hvB := (hbound Y hY).2.2.2.1
  have htδ : |t|≤δ₀ := ht.trans (min_le_left _ _)
  have ht1 : |t|≤1 := ht.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htB : B*|t|≤1 := by
    have hh : |t|≤1/B := ht.trans ((min_le_right _ _).trans (min_le_right _ _))
    nlinarith [(le_div_iff₀ hB).mp hh]
  have hC := hcubic Y hY t (by simpa only [Complex.norm_real,Real.norm_eq_abs] using htδ)
  have hE := real_gaussian_quadratic_error (harmonicVariance Y) B t hv0 hvB hB ht1 htB
  have he : ‖1-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2-Complex.exp (-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2)‖≤(B^2/4)*|t|^3 :=
    (norm_sub_rev _ _).trans_le hE
  have htri := norm_sub_le_norm_sub_add_norm_sub (centeredHarmonic Y t)
    (1-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2) (Complex.exp (-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2))
  have hC' : ‖centeredHarmonic Y t-(1-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2)‖≤A*|t|^3 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hC
  nlinarith
lemma centeredHarmonic_uniform_gaussian_bound : ∃δ β:ℝ,0<δ ∧ 0<β ∧ ∀Y∈Icc (0:ℝ) y₀,∀t:ℝ,|t|≤δ →
    ‖centeredHarmonic Y t‖≤Real.exp (-β*t^2) := by
  obtain ⟨δ₀,A,hδ₀,hA,hcubic⟩ := centeredHarmonic_uniform_cubic
  obtain ⟨c,B,s,hc,hB,hs,hbound⟩ := harmonic_uniform_bounds
  let δ := min δ₀ (min 1 (min (1/B) (c/(4*A))))
  have hδ : 0<δ := by dsimp [δ]; positivity
  refine ⟨δ,c/4,hδ,by positivity,?_⟩
  intro Y hY t ht
  have hv0 : 0≤harmonicVariance Y := (lt_of_lt_of_le hc (hbound Y hY).2.2.1).le
  have hvB := (hbound Y hY).2.2.2.1
  have hvc := (hbound Y hY).2.2.1
  have htδ : |t|≤δ₀ := ht.trans (min_le_left _ _)
  have ht1 : |t|≤1 := ht.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htB : B*|t|≤1 := by
    have hh : |t|≤1/B := ht.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith [(le_div_iff₀ hB).mp hh]
  have htA : A*|t|≤c/4 := by
    have hh : |t|≤c/(4*A) := ht.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have ha4 : 0<4*A := by positivity
    nlinarith [(le_div_iff₀ ha4).mp hh]
  have hlin : ‖1-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2‖=1-harmonicVariance Y/2*t^2 := by
    have he : (1-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2) = ((1-harmonicVariance Y/2*t^2:ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    nlinarith [variance_quadratic_small (harmonicVariance Y) B t hv0 hvB ht1 htB]
  have hC := hcubic Y hY t (by simpa only [Complex.norm_real,Real.norm_eq_abs] using htδ)
  have hC' : ‖centeredHarmonic Y t-(1-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2)‖≤A*|t|^3 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hC
  have htri : ‖centeredHarmonic Y t‖≤‖centeredHarmonic Y t-(1-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2)‖+‖1-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2‖ := by
    have hh := norm_add_le (centeredHarmonic Y t-(1-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2)) (1-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2)
    have he : centeredHarmonic Y t-(1-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2)+(1-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2)=centeredHarmonic Y t := by ring
    rw [he] at hh
    exact hh
  rw [hlin] at htri
  have habs : |t|^3=|t| *t^2 := by rw [pow_succ,sq_abs]; ring
  rw [habs] at hC'
  have hpoly : ‖centeredHarmonic Y t‖≤1-(c/4)*t^2 := by
    nlinarith [mul_le_mul_of_nonneg_right htA (sq_nonneg t),mul_le_mul_of_nonneg_right hvc (sq_nonneg t)]
  apply hpoly.trans
  rw [show 1-(c/4)*t^2 = -(c/4)*t^2+1 by ring]
  exact Real.add_one_le_exp _
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma nat_mul_scaled_quadratic (h:ℕ)(hh:0<h)(t:ℝ) :
    (h:ℝ)*(t/Real.sqrt (h:ℝ))^2=t^2 := by
  have hh0 : (h:ℝ)≠0 := by exact_mod_cast ne_of_gt hh
  rw [div_pow,Real.sq_sqrt (by positivity : (0:ℝ)≤h)]
  field_simp
lemma nat_mul_scaled_cubic (h:ℕ)(hh:0<h)(t:ℝ) :
    (h:ℝ)*|t/Real.sqrt (h:ℝ)|^3=|t|^3/Real.sqrt (h:ℝ) := by
  let r := Real.sqrt (h:ℝ)
  have hr : 0<r := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hrs : r^2=(h:ℝ) := Real.sq_sqrt (by positivity)
  change (h:ℝ)*|t/r|^3=|t|^3/r
  rw [abs_div,abs_of_pos hr,div_pow,←hrs]
  field_simp
lemma gaussian_base_power (v t:ℝ)(h:ℕ)(hh:0<h) :
    (Complex.exp (-(v:ℂ)/2*((t/Real.sqrt (h:ℝ):ℝ):ℂ)^2))^h =
      Complex.exp (-(v:ℂ)/2*(t:ℂ)^2) := by
  rw [←Complex.exp_nat_mul]
  congr 1
  have he : (h:ℝ)*(-v/2*(t/Real.sqrt (h:ℝ))^2) = -v/2*t^2 := by
    calc (h:ℝ)*(-v/2*(t/Real.sqrt (h:ℝ))^2) = (-v/2)*((h:ℝ)*(t/Real.sqrt (h:ℝ))^2) := by ring
         _ = _ := by rw [nat_mul_scaled_quadratic h hh t]
  exact_mod_cast he
lemma centeredHarmonic_scaled_gaussian_error : ∃δ C:ℝ,0<δ ∧ 0<C ∧ ∀Y∈Icc (0:ℝ) y₀,∀h:ℕ,0<h→∀t:ℝ,
    |t/Real.sqrt (h:ℝ)|≤δ →
      ‖centeredHarmonic Y ((t/Real.sqrt (h:ℝ):ℝ):ℂ)^h-Complex.exp (-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2)‖≤C*|t|^3/Real.sqrt (h:ℝ) := by
  obtain ⟨δ,C,hδ,hC,herror⟩ := centeredHarmonic_uniform_gaussian_error
  obtain ⟨c,B,s,hc,hB,hs,hbound⟩ := harmonic_uniform_bounds
  refine ⟨δ,C,hδ,hC,?_⟩
  intro Y hY h hh t ht
  have hv : 0≤harmonicVariance Y := (lt_of_lt_of_le hc (hbound Y hY).2.2.1).le
  let u : ℝ := t/Real.sqrt (h:ℝ)
  let z : ℂ := Complex.exp (-(harmonicVariance Y:ℂ)/2*(u:ℂ)^2)
  have hz : ‖z‖≤1 := by
    have he : -(harmonicVariance Y:ℂ)/2*(u:ℂ)^2 = ((-harmonicVariance Y/2*u^2:ℝ):ℂ) := by push_cast; rfl
    dsimp [z]
    rw [he,Complex.norm_exp,Complex.ofReal_re]
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hv (sq_nonneg u)]
  have hp := unit_power_difference_bound (centeredHarmonic Y u) z
    (centeredHarmonic_norm_real_le_one Y hY u) hz h
  have hE := herror Y hY u ht
  have hnorm : ‖centeredHarmonic Y u^h-z^h‖≤(h:ℝ)*(C*|u|^3) :=
    hp.trans (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg h))
  have he : z^h=Complex.exp (-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2) := gaussian_base_power _ t h hh
  rw [he] at hnorm
  have hfactor : (h:ℝ)*(C*|u|^3)=C*|t|^3/Real.sqrt (h:ℝ) := by
    dsimp [u]
    calc (h:ℝ)*(C*|t/Real.sqrt (h:ℝ)|^3) = C*((h:ℝ)*|t/Real.sqrt (h:ℝ)|^3) := by ring
         _ = _ := by rw [nat_mul_scaled_cubic h hh t]; ring
  rw [hfactor] at hnorm
  exact hnorm
lemma centeredHarmonic_scaled_gaussian_bound : ∃δ β:ℝ,0<δ ∧ 0<β ∧ ∀Y∈Icc (0:ℝ) y₀,∀h:ℕ,0<h→∀t:ℝ,
    |t/Real.sqrt (h:ℝ)|≤δ → ‖centeredHarmonic Y ((t/Real.sqrt (h:ℝ):ℝ):ℂ)^h‖≤Real.exp (-β*t^2) := by
  obtain ⟨δ,β,hδ,hβ,hbound⟩ := centeredHarmonic_uniform_gaussian_bound
  refine ⟨δ,β,hδ,hβ,?_⟩
  intro Y hY h hh t ht
  rw [norm_pow]
  calc ‖centeredHarmonic Y ((t/Real.sqrt (h:ℝ):ℝ):ℂ)‖^h ≤ (Real.exp (-β*(t/Real.sqrt (h:ℝ))^2))^h := by
          exact pow_le_pow_left₀ (norm_nonneg _) (hbound Y hY (t/Real.sqrt (h:ℝ)) ht) h
       _ = Real.exp (-β*t^2) := by
          rw [←Real.exp_nat_mul]
          congr 1
          calc (h:ℝ)*(-β*(t/Real.sqrt (h:ℝ))^2) = -β*((h:ℝ)*(t/Real.sqrt (h:ℝ))^2) := by ring
               _ = _ := by rw [nat_mul_scaled_quadratic h hh t]
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma centeredHarmonic_powers_uniform_on_bounded (T:ℝ)(hT:0≤T)(ε:ℝ)(hε:0<ε) :
    ∃h₀:ℕ,∀h≥h₀,0<h→∀Y∈Icc (0:ℝ) y₀,∀t:ℝ,|t|≤T →
      ‖centeredHarmonic Y ((t/Real.sqrt (h:ℝ):ℝ):ℂ)^h-Complex.exp (-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2)‖≤ε := by
  obtain ⟨δ,C,hδ,hC,herror⟩ := centeredHarmonic_scaled_gaussian_error
  let D := max 1 (max (T/δ) (C*T^3/ε))
  have hD : 0<D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDδ : T/δ≤D := (le_max_left _ _).trans (le_max_right _ _)
  have hDε : C*T^3/ε≤D := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨h₀,hh₀⟩ := exists_nat_gt (D^2)
  refine ⟨h₀,?_⟩
  intro h hh0 hh Y hY t ht
  let r := Real.sqrt (h:ℝ)
  have hr : 0<r := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hrs : r^2=(h:ℝ) := Real.sq_sqrt (by positivity)
  have hreal : (h₀:ℝ)≤h := by exact_mod_cast hh0
  have hrD : D<r := by nlinarith
  have htδ : |t/Real.sqrt (h:ℝ)|≤δ := by
    change |t/r|≤δ
    rw [abs_div,abs_of_pos hr]
    apply (div_le_iff₀ hr).mpr
    have hTδ := (div_le_iff₀ hδ).mp hDδ
    nlinarith
  have he := herror Y hY h hh t htδ
  apply he.trans
  change C*|t|^3/r≤ε
  apply (div_le_iff₀ hr).mpr
  have ht3 : |t|^3≤T^3 := pow_le_pow_left₀ (abs_nonneg t) ht 3
  have hleft := mul_le_mul_of_nonneg_left ht3 hC.le
  have hright := (div_le_iff₀ hε).mp hDε
  nlinarith
end WP.Analysis
