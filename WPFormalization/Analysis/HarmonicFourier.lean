import WPFormalization.Analysis.HarmonicLaw
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma coeff_eq_unit_circle_integral (f:ℂ→ℂ)
    (hf:DifferentiableOn ℂ f (Metric.closedBall 0 1))(n:ℕ) :
    WP.coeff f n = ((2*Real.pi:ℝ):ℂ)⁻¹ * ∫ θ:ℝ in (0)..(2*Real.pi),
      ((circleMap 0 1 θ)^n)⁻¹*f (circleMap 0 1 θ) := by
  have hi : (∮ z in C(0,1), (1/z^(n+1))*f z) = Complex.I*(∫ θ:ℝ in (0)..(2*Real.pi),
      ((circleMap 0 1 θ)^n)⁻¹*f (circleMap 0 1 θ)) := by
    rw [circleIntegral,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    dsimp only
    rw [deriv_circleMap,smul_eq_mul]
    have hz : circleMap 0 1 θ≠0 := circleMap_ne_center (by norm_num : (1:ℝ)≠0)
    field_simp [pow_succ,hz]
    <;> ring
  rw [coeff_eq_circleIntegral f 1 (by norm_num) hf n,hi,←mul_assoc]
  congr 1
  push_cast
  field_simp
lemma circleMap_inverse_pow (θ:ℝ)(n:ℕ) :
    ((circleMap 0 1 θ)^n)⁻¹ = Complex.exp (-(n:ℂ)*(θ:ℂ)*Complex.I) := by
  simp only [circleMap,Complex.ofReal_one,one_mul,zero_add]
  rw [←Complex.exp_nat_mul,←Complex.exp_neg]
  congr 1
  ring
lemma coeff_eq_fourier_integral (f:ℂ→ℂ)
    (hf:DifferentiableOn ℂ f (Metric.closedBall 0 1))(n:ℕ) :
    WP.coeff f n = ((2*Real.pi:ℝ):ℂ)⁻¹ * ∫ θ:ℝ in (0)..(2*Real.pi),
      Complex.exp (-(n:ℂ)*(θ:ℂ)*Complex.I)*f (Complex.exp ((θ:ℂ)*Complex.I)) := by
  rw [coeff_eq_unit_circle_integral f hf n]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  rw [circleMap_inverse_pow]
  simp only [circleMap,Complex.ofReal_one,one_mul,zero_add]
lemma harmonicSumMass_fourier (Y:ℝ)(hY:Y∈Icc 0 y₀)(h m:ℕ) :
    harmonicSumMass Y h m = (2*Real.pi)⁻¹ * ∫ θ:ℝ in (0)..(2*Real.pi),
      (Complex.exp (-(m:ℂ)*(θ:ℂ)*Complex.I)*(harmonicPGF Y (Complex.exp ((θ:ℂ)*Complex.I)))^h).re := by
  obtain ⟨η,hη,hzero⟩ := barH_uniform_zero_free
  have hdiff : DifferentiableOn ℂ (fun w=>harmonicPGF Y w^h) (Metric.closedBall 0 1) :=
    ((harmonicPGF_diffOn hη hzero Y hY).mono (Metric.closedBall_subset_closedBall (by linarith))).pow h
  unfold harmonicSumMass realCoeff
  rw [coeff_eq_fourier_integral _ hdiff m]
  have hc : Continuous (fun θ:ℝ => Complex.exp (-(m:ℂ)*(θ:ℂ)*Complex.I)*(harmonicPGF Y (Complex.exp ((θ:ℂ)*Complex.I)))^h) := by
    have hh : Continuous (fun θ:ℝ=>harmonicPGF Y (Complex.exp ((θ:ℂ)*Complex.I))) := by
      have hf := (harmonicPGF_diffOn hη hzero Y hY).continuousOn
      have hs : Continuous (fun θ:ℝ=>Complex.exp ((θ:ℂ)*Complex.I)) := by fun_prop
      exact continuousOn_univ.mp (hf.comp hs.continuousOn (fun θ _=>by
        rw [Metric.mem_closedBall,dist_zero_right,Complex.norm_exp]
        simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,mul_zero,zero_mul,sub_zero,Real.exp_zero]
        linarith))
    fun_prop
  simp only [←Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  congr 1
  exact (intervalIntegral.intervalIntegral_re (hc.intervalIntegrable (μ:=volume) 0 (2*Real.pi))).symm
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
noncomputable def harmonicCharacteristic (Y t:ℝ) : ℂ := harmonicPGF Y (Complex.exp ((t:ℂ)*Complex.I))
lemma harmonicCharacteristic_hasSum (Y:ℝ)(hY:Y∈Icc 0 y₀)(t:ℝ) :
    HasSum (fun m:ℕ=>(harmonicMass Y m:ℂ)*Complex.exp ((m:ℂ)*(t:ℂ)*Complex.I)) (harmonicCharacteristic Y t) := by
  obtain ⟨η,hη,hzero⟩ := barH_uniform_zero_free
  have hs := hasSum_coeff_on_ball (harmonicPGF Y) (1+η)
    ((harmonicPGF_diffOn hη hzero Y hY).mono Metric.ball_subset_closedBall)
    (Complex.exp ((t:ℂ)*Complex.I)) (by rw [Complex.norm_exp]; simpa using hη)
  have hcoeff (m:ℕ) : WP.coeff (harmonicPGF Y) m = (harmonicMass Y m:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using harmonicPGF_realCoefficients Y hY m
  unfold harmonicCharacteristic
  convert hs using 1
  ext m
  rw [hcoeff,←Complex.exp_nat_mul]
  congr 2
  ring
lemma harmonicCharacteristic_norm_le_one (Y:ℝ)(hY:Y∈Icc 0 y₀)(t:ℝ) : ‖harmonicCharacteristic Y t‖≤1 := by
  apply (harmonicCharacteristic_hasSum Y hY t).norm_le_of_bounded (harmonicMass_hasSum Y hY)
  intro m
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (harmonicMass_pos Y hY m),Complex.norm_exp]
  simp only [Complex.mul_re,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,zero_add,Real.exp_zero,mul_one]
  exact le_rfl
lemma shifted_power_le_exp (t:ℝ)(ht:0<t)(q m:ℕ) :
    ((m:ℝ)+2)^q ≤ ((q.factorial:ℝ)/t^q*Real.exp (2*t))*Real.exp (t*m) := by
  have hpow := Real.pow_div_factorial_le_exp (t*((m:ℝ)+2)) (by positivity) q
  have htq : t^q≠0 := ne_of_gt (pow_pos ht q)
  have hq : (q.factorial:ℝ)≠0 := by exact_mod_cast q.factorial_ne_zero
  calc ((m:ℝ)+2)^q = (t*((m:ℝ)+2))^q/(q.factorial:ℝ)*((q.factorial:ℝ)/t^q) := by rw [mul_pow]; field_simp
       _ ≤ Real.exp (t*((m:ℝ)+2))*((q.factorial:ℝ)/t^q) := mul_le_mul_of_nonneg_right hpow (by positivity)
       _ = _ := by rw [show t*((m:ℝ)+2)=2*t+t*m by ring,Real.exp_add]; ring
lemma harmonic_shifted_moments_uniform (q:ℕ) : ∃C:ℝ,0<C ∧ ∀Y∈Icc (0:ℝ) y₀,
    Summable (fun m:ℕ=>((m:ℝ)+2)^q*harmonicMass Y m) ∧
    ∑'m:ℕ,((m:ℝ)+2)^q*harmonicMass Y m≤C := by
  obtain ⟨t,B,ht,hB,hbound⟩ := harmonicMass_exponential_uniform
  let D := (q.factorial:ℝ)/t^q*Real.exp (2*t)
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨D*B,mul_pos hD hB,?_⟩
  intro Y hY
  have hs := (hbound Y hY).1
  have hS : Summable (fun m:ℕ=>((m:ℝ)+2)^q*harmonicMass Y m) :=
    Summable.of_nonneg_of_le (fun m=>by positivity [harmonicMass_pos Y hY m])
      (fun m=>by simpa only [D,mul_assoc] using mul_le_mul_of_nonneg_right (shifted_power_le_exp t ht q m) (harmonicMass_pos Y hY m).le)
      (hs.summable.mul_left D)
  refine ⟨hS,?_⟩
  calc (∑'m:ℕ,((m:ℝ)+2)^q*harmonicMass Y m) ≤ ∑'m:ℕ,D*(Real.exp (t*m)*harmonicMass Y m) :=
          Summable.tsum_le_tsum
            (fun m=>by simpa only [D,mul_assoc] using mul_le_mul_of_nonneg_right (shifted_power_le_exp t ht q m) (harmonicMass_pos Y hY m).le)
            hS (hs.summable.mul_left D)
       _ = D*(harmonicPGF Y (Real.exp t)).re := by rw [tsum_mul_left,hs.tsum_eq]
       _ ≤ D*B := mul_le_mul_of_nonneg_left (hbound Y hY).2 hD.le
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma probability_power_series_minorization (p:ℕ→ℝ)(hp:∀n,0≤p n)(hs:HasSum p 1)
    (z value:ℂ)(hz:‖z‖=1)(hv:HasSum (fun n:ℕ=>(p n:ℂ)*z^n) value)
    (c:ℝ)(hc:0≤c)(hc0:c≤p 0)(hc1:c≤p 1) :
    ‖value‖ ≤ c*‖1+z‖+1-2*c := by
  let r (n:ℕ):ℝ := p n-(if n=0 then c else 0)-(if n=1 then c else 0)
  have hr (n:ℕ) : 0≤r n := by
    dsimp [r]
    by_cases h0:n=0
    · subst n; simp; linarith
    · by_cases h1:n=1
      · subst n; simp; linarith
      · simpa only [if_neg h0,if_neg h1,sub_zero] using hp n
  have hrS : HasSum r (1-c-c) := hs.sub (hasSum_ite_eq 0 c) |>.sub (hasSum_ite_eq 1 c)
  have hSc := hv.sub (hasSum_ite_eq 0 (c:ℂ)) |>.sub (hasSum_ite_eq 1 ((c:ℂ)*z))
  have hrSc : HasSum (fun n:ℕ=>(r n:ℂ)*z^n) (value-(c:ℂ)-(c:ℂ)*z) := by
    convert hSc using 1
    ext n
    dsimp [r]
    by_cases h0:n=0
    · subst n; simp
    · by_cases h1:n=1
      · subst n; simp; ring
      · simp only [if_neg h0,if_neg h1,sub_zero,Complex.ofReal_sub,Complex.ofReal_zero]
  have hNr : ‖value-(c:ℂ)-(c:ℂ)*z‖ ≤ 1-c-c := hrSc.norm_le_of_bounded hrS (fun n=>by
    rw [norm_mul,norm_pow,hz,one_pow,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hr n)])
  have htri := norm_add_le ((c:ℂ)*(1+z)) (value-(c:ℂ)-(c:ℂ)*z)
  have he : (c:ℂ)*(1+z)+(value-(c:ℂ)-(c:ℂ)*z)=value := by ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc] at htri
  linarith
lemma norm_one_add_unit_lt_two (z:ℂ)(hz:‖z‖=1)(hne:z≠1) : ‖1+z‖<2 := by
  have hpar := parallelogram_law_with_norm ℝ (1:ℂ) z
  simp only [norm_one,hz,one_pow] at hpar
  have hd : 0<‖(1:ℂ)-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  nlinarith [norm_nonneg (1+z),sq_pos_of_pos hd]
lemma harmonicCharacteristic_strict_norm_lt_one (Y:ℝ)(hY:Y∈Icc 0 y₀)(t:ℝ)
    (ht:t∈Icc (-Real.pi) Real.pi)(ht0:t≠0) : ‖harmonicCharacteristic Y t‖<1 := by
  let z := Complex.exp ((t:ℂ)*Complex.I)
  have hz : ‖z‖=1 := Complex.norm_exp_ofReal_mul_I t
  have hzne : z≠1 := by
    intro he
    have hc : Real.cos t=1 := by simpa only [z,Complex.exp_ofReal_mul_I_re,Complex.one_re] using congrArg Complex.re he
    have ht2 : -(2*Real.pi)<t ∧ t<2*Real.pi := by constructor <;> linarith [Real.pi_pos,ht.1,ht.2]
    exact ht0 ((Real.cos_eq_one_iff_of_lt_of_lt ht2.1 ht2.2).mp hc)
  let c := min (harmonicMass Y 0) (harmonicMass Y 1)
  have hc : 0<c := lt_min (harmonicMass_pos Y hY 0) (harmonicMass_pos Y hY 1)
  have hv : HasSum (fun n:ℕ=>(harmonicMass Y n:ℂ)*z^n) (harmonicCharacteristic Y t) := by
    convert harmonicCharacteristic_hasSum Y hY t using 1
    ext n
    dsimp [z]
    rw [←Complex.exp_nat_mul]
    congr 2
    ring
  have hb := probability_power_series_minorization (harmonicMass Y) (fun n=>(harmonicMass_pos Y hY n).le)
    (harmonicMass_hasSum Y hY) z (harmonicCharacteristic Y t) hz hv c hc.le (min_le_left _ _) (min_le_right _ _)
  have hnorm := norm_one_add_unit_lt_two z hz hzne
  nlinarith
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma harmonicCharacteristic_joint_continuous :
    Continuous (fun p:Icc (0:ℝ) y₀ × ℝ => harmonicCharacteristic (p.1:ℝ) p.2) := by
  obtain ⟨η,hη,hzero⟩ := barH_uniform_zero_free
  have hm : Continuous (fun p:Icc (0:ℝ) y₀ × ℝ => Complex.exp ((p.2:ℂ)*Complex.I)) := by fun_prop
  have hmem (p:Icc (0:ℝ) y₀ × ℝ) : Complex.exp ((p.2:ℂ)*Complex.I)∈Metric.closedBall 0 (1+η) := by
    rw [Metric.mem_closedBall,dist_zero_right,Complex.norm_exp_ofReal_mul_I]
    linarith
  have hmap : Continuous (fun p:Icc (0:ℝ) y₀ × ℝ =>
      (p.1,(⟨Complex.exp ((p.2:ℂ)*Complex.I),hmem p⟩:Metric.closedBall (0:ℂ) (1+η)))) :=
    continuous_fst.prodMk (hm.subtype_mk _)
  exact (harmonicPGF_joint_closed hη hzero).comp hmap
lemma harmonicCharacteristic_uniform_gap (δ:ℝ)(hδ:0<δ)(hδπ:δ≤Real.pi) :
    ∃ρ:ℝ,0≤ρ ∧ ρ<1 ∧ ∀Y∈Icc (0:ℝ) y₀,∀t∈Icc (-Real.pi) Real.pi,
      δ≤|t| → ‖harmonicCharacteristic Y t‖≤ρ := by
  let S : Set (Icc (0:ℝ) y₀ × ℝ) := univ ×ˢ (Icc (-Real.pi) Real.pi ∩ {t:ℝ | δ≤|t|})
  have hS : IsCompact S := isCompact_univ.prod (isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs))
  have hSne : S.Nonempty := by
    refine ⟨(⟨0,le_rfl,y₀_pos.le⟩,Real.pi),mem_univ _,⟨?_,?_⟩⟩
    · exact ⟨by linarith [Real.pi_pos],le_rfl⟩
    · change δ≤|Real.pi|
      simpa only [abs_of_pos Real.pi_pos] using hδπ
  obtain ⟨p,hp,hmax⟩ := hS.exists_isMaxOn hSne harmonicCharacteristic_joint_continuous.norm.continuousOn
  have hpt : p.2∈Icc (-Real.pi) Real.pi ∧ δ≤|p.2| := hp.2
  have hpt0 : p.2≠0 := by intro he; rw [he,abs_zero] at hpt; linarith [hpt.2]
  refine ⟨‖harmonicCharacteristic (p.1:ℝ) p.2‖,norm_nonneg _,harmonicCharacteristic_strict_norm_lt_one p.1 p.1.property p.2 hpt.1 hpt0,?_⟩
  intro Y hY t ht hdt
  exact (isMaxOn_iff.mp hmax) (⟨Y,hY⟩,t) ⟨mem_univ _,ht,hdt⟩
end WP.Analysis
