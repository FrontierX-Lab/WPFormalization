import WPFormalization.Intersection.PureZeroBounds
import WPFormalization.Intersection.CriticalCoefficient
import WPFormalization.Intersection.NormalizedBackground
import WPFormalization.Intersection.BackgroundMerging
import WPFormalization.Analysis.DilatonCoefficients
noncomputable section
namespace WP
lemma background_odd_product {N:ℕ}(l:Fin N→ℕ):
    ((backgroundDegrees l).map (fun k=>(oddFactorial k:ℝ))).prod=
      ∏i,(oddFactorial (i.val+2):ℝ)^(l i):=by
  simpa [doubleWeight,List.map_map,Function.comp_def] using doubleWeight_background l
lemma background_term_pureC (P:PsiTheory)(g:ℕ)(d:List ℕ)(hs:Stable g d.length)
    {N:ℕ}(l:Fin N→ℕ)(v:Fin N→ℝ):
    (d.map (fun k=>(oddFactorial k:ℝ))).prod*pure P g (d++backgroundDegrees l)*
      (∏i,v i^(l i)/(l i).factorial) =
    ((3:ℝ)^(complexity g d.length)*Real.Gamma (complexity g d.length)/4^g)*
      (pureC P g (d++backgroundDegrees l)*(complexity g d.length).ascFactorial (∑i,l i)*
        ∏i,(3*v i/(oddFactorial (i.val+2):ℝ))^(l i)/(l i).factorial):=by
  let h:=complexity g d.length
  let k:=∑i,l i
  have hh:1 ≤ h:=by dsimp[h];unfold complexity;unfold Stable at hs;omega
  have hc:complexity g (d++backgroundDegrees l).length=h+k:=by
    simp only [List.length_append,backgroundDegrees_length]
    dsimp[h,k]
    unfold complexity
    unfold Stable at hs
    omega
  have hG:Real.Gamma h≠0:=(Real.Gamma_pos_of_pos (by exact_mod_cast (show 0<h by omega))).ne'
  have hF:∀i:Fin N,(oddFactorial (i.val+2):ℝ)≠0:=fun i=>by exact_mod_cast (oddFactorial_pos (i.val+2)).ne'
  have hGk:Real.Gamma (h+k:ℕ) = Real.Gamma h*(h.ascFactorial k:ℝ):=(gamma_mul_ascFactorial h k hh).symm
  unfold pureC
  rw [List.map_append,List.prod_append,background_odd_product,hc]
  have hprod:(∏i,(3*v i/(oddFactorial (i.val+2):ℝ))^(l i)/(l i).factorial)=
      3^k*(∏i,v i^(l i)/(l i).factorial)/(∏i,(oddFactorial (i.val+2):ℝ)^(l i)):=by
    calc
      _ = ∏i,(3:ℝ)^(l i)*(v i^(l i)/(l i).factorial)/(oddFactorial (i.val+2):ℝ)^(l i):=by
        apply Finset.prod_congr rfl
        intro i hi
        rw [div_pow,mul_pow]
        ring
      _ = (∏i,(3:ℝ)^(l i))*(∏i,v i^(l i)/(l i).factorial)/(∏i,(oddFactorial (i.val+2):ℝ)^(l i)):=by
        rw [Finset.prod_div_distrib,Finset.prod_mul_distrib]
      _ = _:=by rw [Finset.prod_pow_eq_pow_sum]
  rw [hprod,pow_add,←gamma_mul_ascFactorial h k hh]
  have hA:(h.ascFactorial k:ℝ)≠0:=by
    have hp:0<h.ascFactorial k:=by
      simpa only [Nat.sub_add_cancel hh] using Nat.ascFactorial_pos (h-1) k
    exact_mod_cast hp.ne'
  have hPF:(∏i,(oddFactorial (i.val+2):ℝ)^(l i))≠0:=by
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (hF i))
  dsimp only [h,k] at hG hA ⊢
  field_simp [hG,hA,hPF]
  <;> ring
end WP
namespace WP
lemma normalized_pure_background_sum (P:PsiTheory)(g:ℕ)(d:List ℕ)
    (hs:Stable g d.length)(hd:d.sum ≤ dimension g d.length)(Y:ℝ)(hY:Y∈Set.Ico 0 y₀):
    normalized P g d Y=
      ((3:ℝ)^(complexity g d.length)*Real.Gamma (complexity g d.length)/4^g)*
        ∑l∈backgrounds (deficit g d),pureC P g (d++backgroundDegrees l)*
          ((complexity g d.length).ascFactorial (∑i,l i):ℝ)*
            ∏i,(-realCoeff (barH Y) (i.val+1))^(l i)/(l i).factorial:=by
  rw [normalized_background_sum_interior P g d Y hY,if_pos ⟨hs,hd⟩,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [←mul_assoc,background_term_pureC P g d hs]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  congr 2
  rw [realCoeff_barH_interior Y hY.2.ne (i.val+1)]
  simp only [Nat.add_assoc]
  ring
end WP
namespace WP
lemma background_pureC_bound (P:PsiTheory)(g:ℕ)(d:List ℕ)
    (hs:Stable g d.length)(hd:d.sum ≤ dimension g d.length)
    (l:Fin (deficit g d)→ℕ)(hl:l∈backgrounds (deficit g d)):
    pureC P g (d++backgroundDegrees l) ≤ (2:ℝ)^(d.count 0):=by
  have hst:Stable g (d++backgroundDegrees l).length:=by
    simp only [List.length_append]
    unfold Stable at *
    omega
  have hdim:(d++backgroundDegrees l).sum=dimension g (d++backgroundDegrees l).length:=by
    rw [List.sum_append,background_dimension l hl,List.length_append]
    unfold deficit dimension
    unfold dimension at hd
    unfold Stable at hs
    omega
  have hzero:(backgroundDegrees l).count 0=0:=by
    apply List.count_eq_zero.mpr
    intro hz
    obtain ⟨i,hi,he⟩:=(mem_backgroundDegrees l 0).mp hz
    omega
  have hb:=pureC_zero_bounds P g (d++backgroundDegrees l) hst hdim
  simpa only [List.count_append,hzero,add_zero] using hb.2

lemma normalized_pure_background_upper (P:PsiTheory)(g:ℕ)(d:List ℕ)
    (hs:Stable g d.length)(hd:d.sum ≤ dimension g d.length)(Y:ℝ)(hY:Y∈Set.Ico 0 y₀):
    normalized P g d Y ≤
      ((3:ℝ)^(complexity g d.length)*Real.Gamma (complexity g d.length)/4^g)*
        ((2:ℝ)^(d.count 0)*∑l∈backgrounds (deficit g d),
          ((complexity g d.length).ascFactorial (∑i,l i):ℝ)*
            ∏i,|realCoeff (barH Y) (i.val+1)|^(l i)/(l i).factorial):=by
  have hh:0<complexity g d.length:=by unfold complexity;unfold Stable at hs;omega
  have hpre:0 ≤ ((3:ℝ)^(complexity g d.length)*Real.Gamma (complexity g d.length)/4^g):=by
    have hG:0<Real.Gamma (complexity g d.length):=Real.Gamma_pos_of_pos (by exact_mod_cast hh)
    positivity
  rw [normalized_pure_background_sum P g d hs hd Y hY]
  apply mul_le_mul_of_nonneg_left _ hpre
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hp0:0 ≤ pureC P g (d++backgroundDegrees l):=pureC_nonneg P g _
  have hp:=background_pureC_bound P g d hs hd l hl
  have ha:0 ≤ ((complexity g d.length).ascFactorial (∑i,l i):ℝ):=Nat.cast_nonneg _
  have hprod:(∏i,(-realCoeff (barH Y) (i.val+1))^(l i)/(l i).factorial) ≤
      ∏i,|realCoeff (barH Y) (i.val+1)|^(l i)/(l i).factorial:=by
    calc
      _ ≤ |∏i,(-realCoeff (barH Y) (i.val+1))^(l i)/(l i).factorial|:=le_abs_self _
      _ = _:=by
        simp only [Finset.abs_prod,abs_div,abs_pow,abs_neg]
        apply Finset.prod_congr rfl
        intro i hi
        rw [abs_of_nonneg (show 0 ≤ ((l i).factorial:ℝ) from Nat.cast_nonneg _)]
  calc
    _ ≤ pureC P g (d++backgroundDegrees l)*
        ((complexity g d.length).ascFactorial (∑i,l i):ℝ)*
        (∏i,|realCoeff (barH Y) (i.val+1)|^(l i)/(l i).factorial):=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg hp0 ha)
    _ ≤ _:=by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_right hp
      positivity
end WP
