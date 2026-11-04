import Mathlib

/-! Quantitative multiplication, triple products, quotients and scale shifts for first-order real expansions. These reusable scalar estimates use only standard axioms. -/

noncomputable section
open Set Filter
open scoped Topology

namespace WP.Analysis
lemma first_order_mul_error (a b c d x y M E t : ℝ)
    (hM : 0≤M) (hE : 0≤E) (ht : t∈Set.Icc 0 1)
    (ha : |a|≤M) (hb : |b|≤M) (hc : |c|≤M) (hd : |d|≤M)
    (hx : |x-(a+b*t)|≤E*t^2) (hy : |y-(c+d*t)|≤E*t^2) :
    |x*y-(a*c+(a*d+b*c)*t)| ≤ (M^2+4*M*E+E^2)*t^2 := by
  have ht0 := ht.1
  have ht1 := ht.2
  have ht2 : t^2≤1 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hap : |a+b*t|≤2*M := by
    calc _ ≤ |a|+|b*t| := abs_add_le _ _
         _ = |a|+|b| *t := by rw [abs_mul,abs_of_nonneg ht0]
         _ ≤ M+M*t := add_le_add ha (mul_le_mul_of_nonneg_right hb ht0)
         _ ≤ _ := by nlinarith
  have hyp : |y|≤2*M+E := by
    calc _ = |(y-(c+d*t))+(c+d*t)| := by congr 1;ring
         _ ≤ |y-(c+d*t)|+|c+d*t| := abs_add_le _ _
         _ ≤ E*t^2+(|c|+|d*t|) := add_le_add hy (abs_add_le _ _)
         _ = E*t^2+(|c|+|d| *t) := by rw [abs_mul,abs_of_nonneg ht0]
         _ ≤ E*t^2+(M+M*t) := add_le_add le_rfl (add_le_add hc (mul_le_mul_of_nonneg_right hd ht0))
         _ ≤ _ := by nlinarith [mul_nonneg hE (sub_nonneg.mpr ht2),mul_nonneg hM (sub_nonneg.mpr ht1)]
  have hbd : |b*d|≤M^2 := by rw [abs_mul,pow_two];exact mul_le_mul hb hd (abs_nonneg _) hM
  have heq : x*y-(a*c+(a*d+b*c)*t)=
      (x-(a+b*t))*y+(a+b*t)*(y-(c+d*t))+b*d*t^2 := by ring
  rw [heq]
  calc _ ≤ |(x-(a+b*t))*y|+|(a+b*t)*(y-(c+d*t))|+|b*d*t^2| := by
         exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
       _ = |x-(a+b*t)| *|y|+|a+b*t| *|y-(c+d*t)|+|b*d| *t^2 := by
         rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (sq_nonneg t)]
       _ ≤ (E*t^2)*(2*M+E)+(2*M)*(E*t^2)+M^2*t^2 :=
         add_le_add (add_le_add (mul_le_mul hx hyp (abs_nonneg _) (by positivity))
           (mul_le_mul hap hy (abs_nonneg _) (by positivity)))
           (mul_le_mul_of_nonneg_right hbd (sq_nonneg t))
       _ = _ := by ring

lemma first_order_triple_error (a b c d e f x y z M E t : ℝ)
    (hM : 1≤M) (hE : 0≤E) (ht : t∈Set.Icc 0 1)
    (ha : |a|≤M) (hb : |b|≤M) (hc : |c|≤M) (hd : |d|≤M) (he : |e|≤M) (hf : |f|≤M)
    (hx : |x-(a+b*t)|≤E*t^2) (hy : |y-(c+d*t)|≤E*t^2) (hz : |z-(e+f*t)|≤E*t^2) :
    |x*y*z-(a*c*e+(a*c*f+(a*d+b*c)*e)*t)| ≤
      6*(1+M+E+3*M^2+(M^2+4*M*E+E^2))^2*t^2 := by
  have hM0 : 0≤M := by linarith
  let K := M^2+4*M*E+E^2
  have hK : 0≤K := by dsimp [K];positivity
  let B := 1+M+E+3*M^2+K
  have hB : 0≤B := by dsimp [B];positivity
  have hMB : M≤B := by dsimp [B];nlinarith
  have hEB : E≤B := by dsimp [B];nlinarith
  have hKB : K≤B := by dsimp [B];nlinarith
  have hM2B : M^2≤B := by dsimp [B];nlinarith
  have h2M2B : 2*M^2≤B := by dsimp [B];nlinarith
  have hac : |a*c|≤M^2 := by rw [abs_mul,pow_two];exact mul_le_mul ha hc (abs_nonneg _) hM0
  have hcoef : |a*d+b*c|≤2*M^2 := by
    calc _ ≤ |a*d|+|b*c| := abs_add_le _ _
         _ = |a| *|d|+|b| *|c| := by rw [abs_mul,abs_mul]
         _ ≤ M*M+M*M := add_le_add (mul_le_mul ha hd (abs_nonneg _) hM0) (mul_le_mul hb hc (abs_nonneg _) hM0)
         _ = _ := by ring
  have hxy := first_order_mul_error a b c d x y M E t hM0 hE ht ha hb hc hd hx hy
  have hxye : |x*y-(a*c+(a*d+b*c)*t)|≤B*t^2 := hxy.trans (mul_le_mul_of_nonneg_right hKB (sq_nonneg t))
  have hze : |z-(e+f*t)|≤B*t^2 := hz.trans (mul_le_mul_of_nonneg_right hEB (sq_nonneg t))
  have hprod := first_order_mul_error (a*c) (a*d+b*c) e f (x*y) z B B t hB hB ht
    (hac.trans hM2B) (hcoef.trans h2M2B) (he.trans hMB) (hf.trans hMB) hxye hze
  convert hprod using 1 <;> dsimp [B,K] <;> ring
end WP.Analysis
namespace WP.Analysis
lemma first_order_ratio_error (A ax ay au av ar L x y u v r a M E t : ℝ)
    (ha : 0<a) (hM : 1≤M) (hE : 0≤E) (ht : t∈Set.Icc 0 1)
    (hA : |A|≤M) (hax : |ax|≤M) (hay : |ay|≤M) (hau : |au|≤M) (hav : |av|≤M)
    (har : |ar|≤M) (hL : |L|≤M) (hxl : a/2≤x) (hyl : a/2≤y)
    (hx : |x-(A+ax*t)|≤E*t^2) (hy : |y-(A+ay*t)|≤E*t^2)
    (hu : |u-(A+au*t)|≤E*t^2) (hv : |v-(A+av*t)|≤E*t^2)
    (hr : |r-(1+ar*t)|≤E*t^2) (hcoef : ar*A+au+av=L*A+ax+ay) :
    |r*u*v/(x*y)-(1+L*t)| ≤
      (48*(1+M+E+3*M^2+(M^2+4*M*E+E^2))^2/a^2)*t^2 := by
  let B := 1+M+E+3*M^2+(M^2+4*M*E+E^2)
  let K := 6*B^2
  have hK : 0≤K := by dsimp [K];positivity
  have hnum := first_order_triple_error 1 ar A au A av r u v M E t hM hE ht
    (by simpa using hM) har hA hau hA hav hr hu hv
  have hden := first_order_triple_error 1 L A ax A ay (1+L*t) x y M E t hM hE ht
    (by simpa using hM) hL hA hax hA hay (by simpa using mul_nonneg hE (sq_nonneg t)) hx hy
  simp only [one_mul] at hnum hden
  have hlin : A*av+(au+ar*A)*A=A*ay+(ax+L*A)*A := by
    have hi := congrArg (fun z : ℝ => A*z) hcoef
    nlinarith only [hi]
  rw [hlin] at hnum
  let P := A*A+(A*ay+(ax+L*A)*A)*t
  have hN : |r*u*v-(1+L*t)*x*y|≤2*K*t^2 := by
    calc _ ≤ |r*u*v-P|+|P-(1+L*t)*x*y| := abs_sub_le _ _ _
         _ = |r*u*v-P|+|(1+L*t)*x*y-P| := by rw [abs_sub_comm P]
         _ ≤ K*t^2+K*t^2 := add_le_add hnum hden
         _ = _ := by ring
  have hxp : 0<x := by linarith
  have hyp : 0<y := by linarith
  have hxy : a^2/4≤x*y := by nlinarith [mul_le_mul hxl hyl (by linarith : 0≤a/2) hxp.le]
  have hRatio : r*u*v/(x*y)-(1+L*t)=(r*u*v-(1+L*t)*x*y)/(x*y) := by field_simp
  rw [hRatio,abs_div,abs_of_pos (mul_pos hxp hyp)]
  calc _ ≤ (2*K*t^2)/(x*y) := div_le_div_of_nonneg_right hN (mul_pos hxp hyp).le
       _ ≤ (2*K*t^2)/(a^2/4) := div_le_div_of_nonneg_left (by positivity) (by positivity) hxy
       _ = _ := by dsimp [K,B];field_simp <;> ring

lemma first_order_shift_error (x a b h d B E : ℝ)
    (hh : 0<h) (hd : 0≤d) (hB : 0≤B) (hE : 0≤E) (hb : |b|≤B)
    (hx : |x-(a+b/(h+d))|≤E/(h+d)^2) :
    |x-(a+b/h)|≤(E+d*B)/h^2 := by
  have hhd : 0<h+d := by linarith
  have hsquare : h^2≤(h+d)^2 := by nlinarith
  have hprod : h^2≤h*(h+d) := by nlinarith [mul_nonneg hh.le hd]
  have heq : (a+b/(h+d))-(a+b/h)=-(b*d)/(h*(h+d)) := by field_simp <;> ring
  have hcenter : |(a+b/(h+d))-(a+b/h)|≤d*B/h^2 := by
    rw [heq,abs_div,abs_neg,abs_mul,abs_of_nonneg hd,abs_of_pos (mul_pos hh hhd)]
    calc _ ≤ B*d/(h*(h+d)) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hd) (mul_pos hh hhd).le
         _ ≤ (B*d)/h^2 := div_le_div_of_nonneg_left (mul_nonneg hB hd) (sq_pos_of_pos hh) hprod
         _ = _ := by ring
  calc _ ≤ |x-(a+b/(h+d))|+|(a+b/(h+d))-(a+b/h)| := abs_sub_le _ _ _
       _ ≤ E/(h+d)^2+d*B/h^2 := add_le_add hx hcenter
       _ ≤ E/h^2+d*B/h^2 := add_le_add (div_le_div_of_nonneg_left hE (sq_pos_of_pos hh) hsquare) le_rfl
       _ = _ := by ring
end WP.Analysis
