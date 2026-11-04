import Mathlib
/-! Endpoint-uniform logarithmic comparison of the actual one-boundary model: LogModelElementary. -/
noncomputable section
namespace WP.Coefficients
lemma nat_xlog_two_increment (n:ℕ):
    0≤((n:ℝ)+2)*Real.log ((n:ℝ)+2)-(n:ℝ)*Real.log n∧
      ((n:ℝ)+2)*Real.log ((n:ℝ)+2)-(n:ℝ)*Real.log n≤2*Real.log ((n:ℝ)+2)+2:=by
  by_cases hn:n=0
  · subst n
    have hlog:0≤Real.log (2:ℝ):=Real.log_nonneg (by norm_num)
    norm_num only[Nat.cast_zero,zero_add,zero_mul,sub_zero]
    constructor <;>linarith
  · have hnpos:0<(n:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero hn
    let q:ℝ:=((n:ℝ)+2)/n
    have hq0:0<q:=by dsimp[q];positivity
    have hq1:1≤q:=(le_div_iff₀ hnpos).mpr (by linarith)
    have hlogq:0≤Real.log q:=Real.log_nonneg hq1
    have hlogx:0≤Real.log ((n:ℝ)+2):=Real.log_nonneg (by linarith)
    have hsplit:Real.log ((n:ℝ)+2)=Real.log (n:ℝ)+Real.log q:=by
      dsimp[q]
      rw[Real.log_div (by positivity:((n:ℝ)+2)≠0) hnpos.ne']
      ring
    have hqbound:(n:ℝ)*Real.log q≤2:=by
      have ht:=mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hq0) hnpos.le
      have he:(n:ℝ)*(q-1)=2:=by dsimp[q];field_simp;ring
      rwa[he] at ht
    have hid:((n:ℝ)+2)*Real.log ((n:ℝ)+2)-(n:ℝ)*Real.log n=
      2*Real.log ((n:ℝ)+2)+(n:ℝ)*Real.log q:=by rw[hsplit];ring
    rw[hid]
    constructor
    · exact add_nonneg (by positivity) (mul_nonneg hnpos.le hlogq)
    · linarith
lemma log_bounded_nat_scale (g n:ℕ)(hg:1≤g)(hn:n≤3*g):
    Real.log ((n:ℝ)+2)≤3*Real.log ((g:ℝ)+1):=by
  have hgr:(1:ℝ)≤g:=by exact_mod_cast hg
  have hnr:(n:ℝ)≤3*g:=by exact_mod_cast hn
  have hquad:(4:ℝ)≤((g:ℝ)+1)^2:=by nlinarith
  have hmul:=mul_le_mul_of_nonneg_right hquad (by positivity:(0:ℝ)≤(g:ℝ)+1)
  have hc:((g:ℝ)+1)^2*((g:ℝ)+1)=((g:ℝ)+1)^3:=by ring
  rw[hc] at hmul
  have hbig:(n:ℝ)+2≤((g:ℝ)+1)^3:=by linarith
  have ht:=Real.log_le_log (by positivity:(0:ℝ)<(n:ℝ)+2) hbig
  simpa only[Real.log_pow,Nat.cast_ofNat] using ht
lemma nat_xlog_two_increment_uniform:
    ∃C:ℝ,0<C∧∀g n:ℕ,1≤g→n≤3*g→
      |((n:ℝ)+2)*Real.log ((n:ℝ)+2)-(n:ℝ)*Real.log n|≤C*Real.log ((g:ℝ)+1):=by
  let C:ℝ:=6+2/Real.log 2
  have hl2:0<Real.log 2:=Real.log_pos (by norm_num)
  refine ⟨C,by dsimp[C];positivity,?_⟩
  intro g n hg hn
  have hgr:(1:ℝ)≤g:=by exact_mod_cast hg
  obtain ⟨hlo,hup⟩:=nat_xlog_two_increment n
  have hlog:=log_bounded_nat_scale g n hg hn
  have hgl:Real.log 2≤Real.log ((g:ℝ)+1):=Real.log_le_log (by norm_num) (by linarith)
  have ht:=mul_le_mul_of_nonneg_left hgl (show 0≤2/Real.log 2 by positivity)
  have hc:2/Real.log 2*Real.log 2=2:=by field_simp
  rw[hc] at ht
  rw[abs_of_nonneg hlo]
  dsimp[C]
  nlinarith
lemma nat_xlog_double_identity (n:ℕ):
    (n:ℝ)*Real.log (2*(n:ℝ))=(n:ℝ)*Real.log n+(n:ℝ)*Real.log 2:=by
  by_cases hn:n=0
  · subst n;simp
  · rw[Real.log_mul (by norm_num) (by exact_mod_cast hn)]
    ring
lemma nat_xlog_double_two_increment_uniform:
    ∃C:ℝ,0<C∧∀g n:ℕ,1≤g→n≤3*g→
      |((n:ℝ)+2)*Real.log (2*((n:ℝ)+2))-(n:ℝ)*Real.log (2*(n:ℝ))|≤C*Real.log ((g:ℝ)+1):=by
  obtain ⟨C,hC,hinc⟩:=nat_xlog_two_increment_uniform
  refine ⟨C+2,by positivity,?_⟩
  intro g n hg hn
  have hgr:(1:ℝ)≤g:=by exact_mod_cast hg
  have hlo:0≤Real.log 2:=Real.log_nonneg (by norm_num)
  have hgl:Real.log 2≤Real.log ((g:ℝ)+1):=Real.log_le_log (by norm_num) (by linarith)
  have he:((n:ℝ)+2)*Real.log (2*((n:ℝ)+2))-(n:ℝ)*Real.log (2*(n:ℝ))=
      (((n:ℝ)+2)*Real.log ((n:ℝ)+2)-(n:ℝ)*Real.log n)+2*Real.log 2:=by
    have h1:=nat_xlog_double_identity (n+2)
    norm_num only[Nat.cast_add,Nat.cast_ofNat] at h1
    rw[h1,nat_xlog_double_identity]
    ring
  rw[he]
  have ht:=abs_add_le (((n:ℝ)+2)*Real.log ((n:ℝ)+2)-(n:ℝ)*Real.log n) (2*Real.log 2)
  rw[abs_of_nonneg (by positivity:0≤2*Real.log 2)] at ht
  have hi:=hinc g n hg hn
  nlinarith
end WP.Coefficients
namespace WP.Coefficients
lemma xlog_div_scale_identity (g x c:ℝ)(hg:0<g)(hx:0≤x)(hc:0<c):
    g*((x/g)*Real.log (c*(x/g)))=x*Real.log (c*x)-x*Real.log g:=by
  by_cases hx0:x=0
  · subst x;simp
  · have hxpos:0<x:=lt_of_le_of_ne hx (Ne.symm hx0)
    have he:c*(x/g)=(c*x)/g:=by ring
    rw[he,Real.log_div (mul_pos hc hxpos).ne' hg.ne']
    field_simp
    <;>ring
lemma degree_profile_scale_algebra (g k U Z:ℝ)(hg:0<g)(hk:0≤k)(hkg:k≤3*g):
    (2*g)*U-(3*g-k)*Z+(3*g-k)*Real.log (3*g-k)+
      (3*g)*Real.log (6*g)-k*Real.log (2*k)-2*(3*g-k)*Real.log g-2*(3*g-k)=
      g*(2*U-(3-k/g)*Z+(3-k/g)*Real.log (3-k/g)+
        3*Real.log 6-(k/g)*Real.log (2*(k/g))-2*(3-k/g)):=by
  have hm:3-k/g=(3*g-k)/g:=by field_simp <;> ring
  have hmu:g*(3-k/g)=3*g-k:=by field_simp <;> ring
  have hmnonneg:0≤3*g-k:=by linarith
  have hscaleM:=xlog_div_scale_identity g (3*g-k) 1 hg hmnonneg (by norm_num)
  simp only[one_mul] at hscaleM
  rw[←hm] at hscaleM
  have hscaleK:=xlog_div_scale_identity g k 2 hg hk (by norm_num)
  have hlog6:Real.log (6*g)=Real.log 6+Real.log g:=Real.log_mul (by norm_num) hg.ne'
  rw[hlog6]
  calc
    _ = 2*g*U-(3*g-k)*Z+g*((3-k/g)*Real.log (3-k/g))+
          3*g*Real.log 6-g*((k/g)*Real.log (2*(k/g)))-2*(3*g-k):=by
      rw[hscaleM,hscaleK]
      ring
    _ = _:=by rw[show 3*g-k=g*(3-k/g) from hmu.symm];ring
end WP.Coefficients
namespace WP.Coefficients
lemma model_ratio_log_cancel (c F A O Q g:ℝ)(m:ℕ)
    (hc:0<c)(hF:0<F)(hA:0<A)(hO:0<O)(hQ:0<Q)(hg:0<g):
    Real.log ((c*F*A/O)/((c/Q)*g^(2*m)))=
      Real.log F+Real.log A+Real.log Q-Real.log O-(2*m:ℕ)*Real.log g:=by
  have he:(c*F*A/O)/((c/Q)*g^(2*m))=F*A*Q/(O*g^(2*m)):=by
    field_simp [hc.ne',hO.ne',hQ.ne',hg.ne']
    <;>ring
  rw[he,Real.log_div (mul_pos (mul_pos hF hA) hQ).ne' (mul_pos hO (pow_pos hg _)).ne',
    Real.log_mul (mul_pos hF hA).ne' hQ.ne',Real.log_mul hF.ne' hA.ne',
    Real.log_mul hO.ne' (pow_pos hg _).ne',Real.log_pow]
  ring
end WP.Coefficients
