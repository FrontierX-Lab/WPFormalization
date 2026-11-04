import WPFormalization.Statements.QuantitativeCuspLocal
import WPFormalization.Volumes.PoissonLeadingDiagonal
/-! The genuine coefficient ratio in (14.9). The proved uniform local-limit
estimate bounds every numerator point mass, including index zero, and gives
a positive lower bound at the exact saddle center. -/
noncomputable section
namespace WP.RandomGeometry
open Set Filter
open scoped Topology

lemma marked_saddle_mass_bounds (P:PsiTheory)(p:ℕ)(hp:1≤ p):
    ∃H:ℝ,0< H ∧ ∀g m:ℕ,∀x∈Ioo (0:ℝ) xCritical,
      (m:ℝ)=(complexity g p:ℝ)*Psi x→
      H≤ min (complexity g p:ℝ) (m:ℝ)→
      let σ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
      1/(2*Real.sqrt (2*Real.pi))≤σ*cuspMass P g p m x ∧
      ∀q:ℕ,σ*cuspMass P g p q x≤3/(2*Real.sqrt (2*Real.pi)):=by
  obtain ⟨C,κ,M₀,hC,hκ,hM₀,hlocal⟩:=quantitative_cusp_local P p hp
  let a:ℝ:=1/Real.sqrt (2*Real.pi)
  have ha:0< a:=by dsimp[a];positivity
  have hlim:Tendsto (fun t:ℝ=> C*Real.rpow t (-κ)) atTop (𝓝 0):=by
    simpa only[Real.rpow_eq_pow,mul_zero] using (tendsto_rpow_neg_atTop hκ).const_mul C
  obtain ⟨H₁,hsmall⟩:=Filter.eventually_atTop.mp (hlim.eventually (eventually_lt_nhds (half_pos ha)))
  let H:ℝ:=max M₀ H₁
  refine ⟨H,hM₀.trans_le (le_max_left _ _),?_⟩
  intro g m x hx hk hsize
  dsimp only
  let h:ℝ:=complexity g p
  let σ:=Real.sqrt (h*euler Psi x)
  let M:ℝ:=min h (m:ℝ)
  have hM:M₀≤ M:=(le_max_left _ _).trans hsize
  have herr:C*Real.rpow M (-κ)≤ a/2:=(hsmall M ((le_max_right _ _).trans hsize)).le
  have hmass(q:ℕ):
      |σ*cuspMass P g p q x-
        Real.exp (-((q:ℝ)-(m:ℝ))^2/(2*σ^2))/Real.sqrt (2*Real.pi)|≤ a/2:=by
    have hl:=hlocal g x hx (by simpa only[←hk] using hM) (q:ℤ)
    simp only[Int.natCast_nonneg,ite_true,Int.toNat_natCast,Int.cast_natCast,←hk] at hl
    exact hl.trans herr
  have hm:|σ*cuspMass P g p m x-a|≤ a/2:=by
    simpa only[sub_self,zero_pow (by norm_num:2≠0),neg_zero,zero_div,Real.exp_zero,a] using hmass m
  refine ⟨?_,?_⟩
  · have hh: a/2≤σ*cuspMass P g p m x:=by linarith only[(abs_le.mp hm).1]
    convert hh using 1 <;> dsimp[a] <;> ring
  · intro q
    have hG:Real.exp (-((q:ℝ)-(m:ℝ))^2/(2*σ^2))/Real.sqrt (2*Real.pi)≤ a:=by
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg _)) (mul_nonneg (by norm_num) (sq_nonneg _)))
    have hq:σ*cuspMass P g p q x≤3*a/2:=by linarith only[(abs_le.mp (hmass q)).2,hG]
    convert hq using 1 <;> dsimp[a] <;> ring

lemma marked_saddle_coefficient_ratio (P:PsiTheory)(p:ℕ)(hp:1≤ p):
    ∃H:ℝ,0< H ∧ ∀g m:ℕ,∀x∈Ioo (0:ℝ) xCritical,
      (m:ℝ)=(complexity g p:ℝ)*Psi x→
      H≤ min (complexity g p:ℝ) (m:ℝ)→
      0< realCoeff (iteratedDeriv p (Phi P g)) m ∧
      ∀j:ℕ,j≤ m→
        realCoeff (iteratedDeriv p (Phi P g)) (m-j)/
          realCoeff (iteratedDeriv p (Phi P g)) m≤3*x^j:=by
  obtain ⟨H,hH,hbound⟩:=marked_saddle_mass_bounds P p hp
  refine ⟨H,hH,?_⟩
  intro g m x hx hk hm
  have hh:0<(complexity g p:ℝ):=hH.trans_le (hm.trans (min_le_left _ _))
  have hs:Stable g p:=by
    have hn:0< complexity g p:=by exact_mod_cast hh
    unfold Stable
    unfold complexity at hn
    omega
  let σ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
  have hσ:0<σ:=Real.sqrt_pos.mpr (mul_pos hh
    (mul_pos hx.1 (Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)))
  have hF:0< markedF P g p x:=markedF_positive_cusp_weight P g p hp hs x ⟨hx.1.le,hx.2⟩
  have hb:=hbound g m x hx hk hm
  have hPm:0< cuspMass P g p m x:=
    (mul_pos_iff_of_pos_left hσ).mp ((by positivity:0<(1:ℝ)/(2*Real.sqrt (2*Real.pi))).trans_le hb.1)
  have ham:0< realCoeff (iteratedDeriv p (Phi P g)) m:=by
    have he:0< realCoeff (iteratedDeriv p (Phi P g)) m*x^m:=
      (div_pos_iff_of_pos_right hF).mp hPm
    exact (mul_pos_iff_of_pos_right (pow_pos hx.1 m)).mp he
  refine ⟨ham,?_⟩
  intro j hj
  have hmass:cuspMass P g p (m-j) x/cuspMass P g p m x≤3:=by
    apply (div_le_iff₀ hPm).mpr
    apply (mul_le_mul_iff_right₀ hσ).mp
    have hn:=hb.2 (m-j)
    have hd:=hb.1
    have he:(3:ℝ)/(2*Real.sqrt (2*Real.pi))=3*(1/(2*Real.sqrt (2*Real.pi))):=by ring
    rw[he] at hn
    dsimp only[σ]
    nlinarith only[hn,hd]
  have hid:realCoeff (iteratedDeriv p (Phi P g)) (m-j)/
      realCoeff (iteratedDeriv p (Phi P g)) m=
      x^j*(cuspMass P g p (m-j) x/cuspMass P g p m x):=by
    have hpow:x^m=x^(m-j)*x^j:=by rw[←pow_add,Nat.sub_add_cancel hj]
    unfold cuspMass
    rw[hpow]
    field_simp [hF.ne',ham.ne',hx.1.ne']
    <;> ring
  rw[hid]
  exact (mul_le_mul_of_nonneg_left hmass (pow_nonneg hx.1.le j)).trans_eq (by ring)

def primitiveSaddleX (g n:ℕ):ℝ:=
  XR (densityY (2*((n-1:ℕ):ℝ)/(2*(g:ℝ)-1)))

lemma primitive_complexity (g:ℕ)(hg:1≤ g):
    (complexity g 1:ℝ)=2*(g:ℝ)-1:=by
  unfold complexity
  rw[Nat.cast_sub (by omega)]
  push_cast
  ring

theorem primitive_coefficient_ratio (P:PsiTheory):
    ∃H:ℝ,0< H ∧ ∀g n:ℕ,1≤ g→
      H≤ min (2*(g:ℝ)-1) ((n-1:ℕ):ℝ)→
      let x:=primitiveSaddleX g n
      x∈Ioo (0:ℝ) xCritical ∧
      0< realCoeff (iteratedDeriv 1 (Phi P g)) (n-1) ∧
      ∀j:ℕ,j≤ n-1→
        realCoeff (iteratedDeriv 1 (Phi P g)) (n-1-j)/
          realCoeff (iteratedDeriv 1 (Phi P g)) (n-1)≤3*x^j:=by
  obtain ⟨H,hH,hbound⟩:=marked_saddle_coefficient_ratio P 1 (by norm_num)
  refine ⟨H,hH,?_⟩
  intro g n hg hsize
  let h:ℝ:=complexity g 1
  let m:ℝ:=(n-1:ℕ)
  have he:=primitive_complexity g hg
  have hh:0< h:=hH.trans_le (hsize.trans (min_le_left _ _)) |>.trans_eq he.symm
  have hm:0< m:=hH.trans_le (hsize.trans (min_le_right _ _))
  have hs:=Analysis.physicalDensitySaddle_spec (m/h) (div_pos hm hh)
  have hxeq:XR (densityY (2*(m/h)))=primitiveSaddleX g n:=by
    dsimp[primitiveSaddleX,m,h]
    rw[he]
    congr 2
    ring
  rw[hxeq] at hs
  have hk:m=(complexity g 1:ℝ)*Psi (primitiveSaddleX g n):=by
    rw[hs.2]
    change m=h*(m/h)
    rw[mul_div_cancel₀ _ hh.ne']
  exact ⟨hs.1,hbound g (n-1) _ hs.1 hk (by simpa only[he] using hsize)⟩

theorem primitive_coefficient_ratio_eventually (P:PsiTheory)(n:ℕ→ℕ)
    (hn:Tendsto n atTop atTop):
    ∀ᶠg:ℕ in atTop,
      let x:=primitiveSaddleX g (n g)
      x∈Ioo (0:ℝ) xCritical ∧
      0< realCoeff (iteratedDeriv 1 (Phi P g)) (n g-1) ∧
      ∀j:ℕ,j≤ n g-1→
        realCoeff (iteratedDeriv 1 (Phi P g)) (n g-1-j)/
          realCoeff (iteratedDeriv 1 (Phi P g)) (n g-1)≤3*x^j:=by
  obtain ⟨H,hH,hbound⟩:=primitive_coefficient_ratio P
  let G:ℕ:=Nat.ceil (H+1)
  have hceil:H+1≤(G:ℝ):=Nat.le_ceil _
  filter_upwards[eventually_ge_atTop (max G 1),hn.eventually_ge_atTop (G+1)] with g hg hng
  have hg1:1≤ g:=(le_max_right _ _).trans hg
  apply hbound g (n g) hg1
  apply le_min
  · have hgG:(G:ℝ)≤ g:=by exact_mod_cast (le_max_left G 1).trans hg
    linarith
  · have hnm:G≤ n g-1:=by omega
    have hnmR:(G:ℝ)≤((n g-1:ℕ):ℝ):=by exact_mod_cast hnm
    linarith
end WP.RandomGeometry
