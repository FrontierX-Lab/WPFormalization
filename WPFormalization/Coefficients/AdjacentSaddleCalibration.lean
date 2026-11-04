import WPFormalization.Coefficients.DegreeProfileRegularity
import WPFormalization.Analysis.KernelZeroValues
import WPFormalization.Statements.Parameter
/-! The original trigonometric saddle equals the actual infimum mean saddle.
The proof uses the exact zero-parameter kernels, and preserves m=N-k even
at m=1. A uniform square-distance bound from the top endpoint follows. -/
noncomputable section
namespace WP.Coefficients
open Set
lemma unscaledMean_trig (t:ℝ) (ht:t∈Ioo (0:ℝ) Real.pi) :
    2*unscaledMean (t^2/2)+trigDensity t=3 := by
  let z:ℝ:=t^2/2
  have hz:z∈Icc (0:ℝ) (r 0) := by
    rw[r_zero_value]
    exact ⟨by positivity,by dsimp[z];nlinarith [ht.1,ht.2,Real.pi_pos]⟩
  have hH:(H 0 (z:ℂ)).re≠0 := (H_zero_re_pos z hz).ne'
  have hs:=congrArg Complex.re (Analysis.rootKernel_sine (t:ℂ))
  have hc:=congrArg Complex.re (K_zero_sine_derivative (t:ℂ))
  have hd:=congrArg Complex.re (kernel_differential 0 (z:ℂ))
  have hzero:((t:ℂ)^2/2)=(z:ℂ) := by dsimp[z];push_cast;rfl
  rw[hzero] at hs hc
  rw[H_zero_eq_K_deriv] at hd
  have hHder:=congrArg Complex.re (H_zero_eq_K_deriv (z:ℂ))
  norm_num [Complex.mul_re,Complex.mul_im] at hs
  change t*(K 0 (z:ℂ)).re=Real.sin t at hs
  have ht2r : ((t:ℂ)^2).re=t^2 := by rw[←Complex.ofReal_pow];rfl
  have ht2i : ((t:ℂ)^2).im=0 := by rw[←Complex.ofReal_pow];rfl
  rw[←Complex.ofReal_cos] at hc
  simp only [Complex.mul_re,Complex.add_re,Complex.ofReal_re,ht2r,ht2i,zero_mul,sub_zero] at hc
  norm_num [Complex.mul_re,Complex.mul_im] at hHder
  have hden : Analysis.trigDen t ≠0 := (Analysis.trigDen_pos t ⟨ht.1,ht.2.le⟩).ne'
  have hdeneq:t^3*(H 0 (z:ℂ)).re=3*Analysis.trigDen t := by
    dsimp[Analysis.trigDen]
    nlinarith only [hs,congrArg (fun q:ℝ=>q*t) hc,congrArg (fun q:ℝ=>q*t^3) hHder]
  have hdiff:=congrArg Complex.re (kernel_differential 0 (z:ℂ))
  norm_num [Complex.mul_re,Complex.mul_im] at hdiff
  change 2*(-z*(deriv (H 0) (z:ℂ)).re/(H 0 (z:ℂ)).re)+
    t^2*Real.sin t/Analysis.trigDen t=3
  field_simp [hH,hden]
  nlinarith only [congrArg (fun q:ℝ=>q*(K 0 (z:ℂ)).re) hdeneq,
    congrArg (fun q:ℝ=>q*Analysis.trigDen t) hdiff,
    congrArg (fun q:ℝ=>q*t^2*(H 0 (z:ℂ)).re) hs,hdeneq]
lemma trigSaddle_square_saddleZeta (g k:ℕ)(hg:1≤g)(hk:k<3*g-2) :
    (trigSaddle g k)^2/2=saddleZeta (((3*g-2-k:ℕ):ℝ)/(complexity g 1:ℝ)) := by
  have ht := trig_saddle_spec g k hg hk
  let t:ℝ := trigSaddle g k
  let h:ℝ := complexity g 1
  let m:ℝ := (3*g-2-k:ℕ)
  have hhr:h=2*(g:ℝ)-1 := by
    have he:complexity g 1+1=2*g := by unfold complexity;omega
    have her:(complexity g 1:ℝ)+1=2*(g:ℝ) := by exact_mod_cast he
    dsimp[h];linarith
  have hhp:0<h := by
    have hgr:(1:ℝ)≤g:=by exact_mod_cast hg
    linarith only [hgr,hhr]
  have hmr:m=3*(g:ℝ)-2-k := by
    dsimp[m]
    rw[Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    push_cast;rfl
  have hmean := unscaledMean_trig t ht.1
  rw[ht.2.1] at hmean
  have he:unscaledMean (t^2/2)=m/h := by
    apply (eq_div_iff hhp.ne').mpr
    have hhh:2*(g:ℝ)-1≠0 := by rw[←hhr];exact hhp.ne'
    field_simp [hhh] at hmean
    rw[hhr,hmr]
    nlinarith only[hmean]
  have hu:m/h∈Icc (0:ℝ) (3/2) := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hhp.le,(div_le_iff₀ hhp).mpr ?_⟩
    have hhg:(1:ℝ)≤g := by exact_mod_cast hg
    have hk0:(0:ℝ)≤k := Nat.cast_nonneg k
    rw[hmr,hhr]
    nlinarith
  have hz:t^2/2∈Icc (0:ℝ) (r 0) := by
    rw[r_zero_value]
    exact ⟨by positivity,by nlinarith [ht.1.1,ht.1.2,Real.pi_pos]⟩
  have hs:=saddleZeta_spec (m/h) hu
  exact unscaledMean_strictMonoOn.injOn hz hs.1 (he.trans hs.2.symm)

lemma saddleZeta_three_halves : saddleZeta (3/2)=r 0 := by
  have hs:=saddleZeta_spec (3/2) (by norm_num: (3/2:ℝ)∈Icc (0:ℝ) (3/2))
  apply unscaledMean_strictMonoOn.injOn hs.1 ⟨(r_pos 0 ⟨le_rfl,y₀_pos⟩).le,le_rfl⟩
  rw[hs.2,unscaledMean_at_r]

lemma trigSaddle_square_endpoint_bound (g k:ℕ)(hg:1≤g)(hk:k<3*g-2) :
    |(trigSaddle g k)^2/Real.pi^2-1|≤(10/Real.pi^2)*((k:ℝ)+1)/g := by
  have ht:=(trig_saddle_spec g k hg hk).1
  have ht2:(trigSaddle g k)^2≤Real.pi^2 := by nlinarith [ht.1,ht.2,Real.pi_pos]
  let h:ℝ:=complexity g 1
  let m:ℝ:=(3*g-2-k:ℕ)
  have hhr:h=2*(g:ℝ)-1 := by
    have he:complexity g 1+1=2*g := by unfold complexity;omega
    have her:(complexity g 1:ℝ)+1=2*(g:ℝ) := by exact_mod_cast he
    dsimp[h];linarith
  have hgr:(0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hgg:(1:ℝ)≤g := by exact_mod_cast hg
  have hhp:0<h := by rw[hhr];linarith
  have hgh:(g:ℝ)≤h := by rw[hhr];linarith
  have hmr:m=3*(g:ℝ)-2-k := by
    dsimp[m]
    rw[Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    push_cast;rfl
  have hu:m/h∈Icc (0:ℝ) (3/2) := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hhp.le,(div_le_iff₀ hhp).mpr ?_⟩
    rw[hmr,hhr]
    nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  have hid:3/2-m/h=((k:ℝ)+1/2)/h := by
    apply (eq_div_iff hhp.ne').mpr
    field_simp [hhp.ne']
    rw[hmr,hhr]
    ring
  have hs:=saddleZeta_ordered_lipschitz (m/h) (3/2) hu (by norm_num) hu.2
  rw[saddleZeta_three_halves,←trigSaddle_square_saddleZeta g k hg hk,r_zero_value,hid] at hs
  have hsq : Real.pi^2-(trigSaddle g k)^2≤10*((k:ℝ)+1)/g := by
    have he:((k:ℝ)+1/2)/h≤((k:ℝ)+1)/g :=
      (div_le_div_of_nonneg_right (by linarith) hhp.le).trans
        (div_le_div_of_nonneg_left (by positivity) hgr hgh)
    calc _ = 2*(Real.pi^2/2-(trigSaddle g k)^2/2) := by ring
         _ ≤ 2*(5*(((k:ℝ)+1/2)/h)) := mul_le_mul_of_nonneg_left hs.2 (by norm_num)
         _ ≤ 10*(((k:ℝ)+1)/g) := by nlinarith only [mul_le_mul_of_nonneg_left he (show 0≤(10:ℝ) by norm_num)]
         _ = _ := by ring
  have hp:0<Real.pi^2 := sq_pos_of_pos Real.pi_pos
  rw[abs_of_nonpos (sub_nonpos.mpr ((div_le_one hp).mpr ht2))]
  calc _ = (Real.pi^2-(trigSaddle g k)^2)/Real.pi^2 := by field_simp <;> ring
       _ ≤ (10*((k:ℝ)+1)/g)/Real.pi^2 := div_le_div_of_nonneg_right hsq hp.le
       _ = _ := by ring

end WP.Coefficients
