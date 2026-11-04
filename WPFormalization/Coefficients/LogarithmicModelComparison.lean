import WPFormalization.Coefficients.LogModelStirling
import WPFormalization.Coefficients.LogModelElementary
import WPFormalization.Coefficients.OneBoundaryModelComparison
import WPFormalization.Coefficients.SaddleActionShift
import WPFormalization.Coefficients.UniformSaddleProof
/-! Endpoint-uniform logarithmic comparison of the actual one-boundary model: LogarithmicModelComparison. -/
noncomputable section
namespace WP.Coefficients
open Set
lemma oneBoundaryModelJ_log_quotient (g k:ℕ)(hg:1≤g)(hk:k≤3*g-2):
    Real.log (oneBoundaryModelJ g k/(oneBoundaryModelJ g (3*g-2)*(g:ℝ)^(2*(3*g-2-k))))=
      Real.log ((3*g-2-k).factorial:ℝ)+Real.log (unscaledCoeff (complexity g 1) (3*g-2-k))+
        Real.log (oddFactorial (3*g-2):ℝ)-Real.log (oddFactorial k:ℝ)-
          (2*(3*g-2-k):ℕ)*Real.log (g:ℝ):=by
  let h:ℕ:=complexity g 1
  let N:ℕ:=3*g-2
  let m:ℕ:=N-k
  have hh:0<h:=by dsimp[h,complexity];omega
  have hG:0<Real.Gamma (h:ℝ):=Real.Gamma_pos_of_pos (by exact_mod_cast hh)
  have hg0:0<(g:ℝ):=by exact_mod_cast (show 0<g by omega)
  have ha:0<unscaledCoeff h m:=unscaledCoeff_pos h m hh
  have hf:0<(m.factorial:ℝ):=by positivity
  have ho:0<(oddFactorial k:ℝ):=by exact_mod_cast oddFactorial_pos k
  have hoN:0<(oddFactorial N:ℝ):=by exact_mod_cast oddFactorial_pos N
  have hcommon:0<(3:ℝ)^h*Real.Gamma h/4^g:=by positivity
  change Real.log (oneBoundaryModelJ g k/(oneBoundaryModelJ g N*(g:ℝ)^(2*m)))=_
  rw[oneBoundaryModelJ_top]
  change Real.log (((3:ℝ)^h*Real.Gamma h/4^g*(m.factorial:ℝ)*unscaledCoeff h m/(oddFactorial k:ℝ))/
    (((3:ℝ)^h*Real.Gamma h/4^g/(oddFactorial N:ℝ))*(g:ℝ)^(2*m)))=_
  exact model_ratio_log_cancel _ _ _ _ _ _ m hcommon hf ha ho hoN hg0
lemma uniform_saddle_action_error:
    ∃C:ℝ,0<C∧∀h m:ℕ,1≤h→2*m≤3*h→
      |Real.log (unscaledCoeff h m)-unscaledSaddleAction h m|≤C*Real.log ((h:ℝ)+1):=by
  obtain ⟨C,hC,herr⟩:=WP.uniform_saddle_proof
  refine ⟨C,hC,?_⟩
  intro h m hh hm
  convert herr h hh m hm using 1
  unfold unscaledSaddleAction unscaledLogPotential
  congr 1
  ring
lemma degree_profile_exact_scaled_action (g k:ℝ)(hg:0<g)(hk:0≤k)(hkg:k≤3*g):
    unscaledSaddleAction (2*g) (3*g-k)+(3*g-k)*Real.log (3*g-k)+
      (3*g)*Real.log (6*g)-k*Real.log (2*k)-2*(3*g-k)*Real.log g-2*(3*g-k)=
      g*logDegreeProfile (k/g):=by
  have hz:(3*g-k)/(2*g)=(3-k/g)/2:=by field_simp <;>ring
  unfold unscaledSaddleAction unscaledLogPotential logDegreeProfile
  rw[hz]
  convert degree_profile_scale_algebra g k
    (-Real.log (H 0 (saddleZeta ((3-k/g)/2))).re) (Real.log (saddleZeta ((3-k/g)/2))) hg hk hkg using 1
  ring
end WP.Coefficients
namespace WP.Coefficients
open Set
lemma log_bounded_nat_successor_scale (g n:ℕ)(hg:1≤g)(hn:n≤3*g):
    Real.log ((n:ℝ)+1)≤3*Real.log ((g:ℝ)+1):=by
  exact (Real.log_le_log (by positivity:(0:ℝ)<(n:ℝ)+1) (by linarith:(n:ℝ)+1≤(n:ℝ)+2)).trans
    (log_bounded_nat_scale g n hg hn)
lemma oneBoundaryModelJ_log_profile_uniform:
    ∃C:ℝ,0<C∧∀g:ℕ,1≤g→∀k:ℕ,k≤3*g-2→
      |Real.log (oneBoundaryModelJ g k/(oneBoundaryModelJ g (3*g-2)*(g:ℝ)^(2*(3*g-2-k))))-
        (g:ℝ)*logDegreeProfile ((k:ℝ)/g)|≤C*Real.log ((g:ℝ)+1):=by
  obtain ⟨CF,hCF,hfactor⟩:=factorial_log_uniform_bound
  obtain ⟨CO,hCO,hodd⟩:=oddFactorial_log_uniform_bound
  obtain ⟨CS,hCS,hsaddle⟩:=uniform_saddle_action_error
  obtain ⟨CT,hCT,hshift⟩:=unscaledSaddleAction_shift_bound
  obtain ⟨CX,hCX,hxinc⟩:=nat_xlog_two_increment_uniform
  obtain ⟨CD,hCD,hdinc⟩:=nat_xlog_double_two_increment_uniform
  have hl2:0<Real.log 2:=Real.log_pos (by norm_num)
  let C:ℝ:=3*CF+3*CS+6*CO+3*CT+CX+CD+4+4/Real.log 2
  refine ⟨C,by dsimp[C];positivity,?_⟩
  intro g hg k hk
  let h:ℕ:=complexity g 1
  let N:ℕ:=3*g-2
  let m:ℕ:=N-k
  have hh:1≤h:=by dsimp[h,complexity];omega
  have hm:2*m+1≤3*h:=by dsimp[m,N,h,complexity];omega
  have hmL:m≤3*g:=by dsimp[m,N];omega
  have hNL:N≤3*g:=by dsimp[N];omega
  have hkL:k≤3*g:=by omega
  have hhL:h≤3*g:=by dsimp[h,complexity];omega
  have hgr:(1:ℝ)≤g:=by exact_mod_cast hg
  have hgR:0<(g:ℝ):=zero_lt_one.trans_le hgr
  have heN:h+1=2*g:=by dsimp[h,complexity];omega
  have heR:(h:ℝ)+1=2*(g:ℝ):=by exact_mod_cast heN
  have hmeN:m+2+k=3*g:=by dsimp[m,N];omega
  have hmeR:(m:ℝ)+2=3*(g:ℝ)-(k:ℝ):=by
    have he:(m:ℝ)+2+(k:ℝ)=3*(g:ℝ):=by exact_mod_cast hmeN
    linarith
  have hNeN:N+2=3*g:=by dsimp[N];omega
  have hNeR:(N:ℝ)+2=3*(g:ℝ):=by exact_mod_cast hNeN
  have hmk:(m:ℝ)+(k:ℝ)=(N:ℝ):=by
    have hn:m+k=N:=by dsimp[m,N];omega
    exact_mod_cast hn
  have hF:|Real.log (m.factorial:ℝ)-((m:ℝ)*Real.log m-m)|≤3*CF*Real.log ((g:ℝ)+1):=by
    exact (hfactor m).trans (by nlinarith[mul_le_mul_of_nonneg_left (log_bounded_nat_successor_scale g m hg hmL) hCF.le])
  have hS:|Real.log (unscaledCoeff h m)-unscaledSaddleAction h m|≤3*CS*Real.log ((g:ℝ)+1):=by
    exact (hsaddle h m hh (by omega)).trans (by nlinarith[mul_le_mul_of_nonneg_left (log_bounded_nat_successor_scale g h hg hhL) hCS.le])
  have hO:|Real.log (oddFactorial N:ℝ)-((N:ℝ)*Real.log (2*(N:ℝ))-N)|≤3*CO*Real.log ((g:ℝ)+1):=by
    exact (hodd N).trans (by nlinarith[mul_le_mul_of_nonneg_left (log_bounded_nat_successor_scale g N hg hNL) hCO.le])
  have hK:|Real.log (oddFactorial k:ℝ)-((k:ℝ)*Real.log (2*(k:ℝ))-k)|≤3*CO*Real.log ((g:ℝ)+1):=by
    exact (hodd k).trans (by nlinarith[mul_le_mul_of_nonneg_left (log_bounded_nat_successor_scale g k hg hkL) hCO.le])
  have hT:|unscaledSaddleAction (2*(g:ℝ)) (3*(g:ℝ)-k)-unscaledSaddleAction h m|≤3*CT*Real.log ((g:ℝ)+1):=by
    have ht:=hshift h hh m hm
    rw[heR,hmeR] at ht
    have hlogh:Real.log (2*(g:ℝ))≤3*Real.log ((g:ℝ)+1):=by
      rw[←heR]
      exact log_bounded_nat_successor_scale g h hg hhL
    exact ht.trans (by nlinarith[mul_le_mul_of_nonneg_left hlogh hCT.le])
  have hX:|(3*(g:ℝ)-k)*Real.log (3*(g:ℝ)-k)-(m:ℝ)*Real.log m|≤CX*Real.log ((g:ℝ)+1):=by
    simpa only[hmeR] using hxinc g m hg hmL
  have hD:|(3*(g:ℝ))*Real.log (6*(g:ℝ))-(N:ℝ)*Real.log (2*(N:ℝ))|≤CD*Real.log ((g:ℝ)+1):=by
    have ht:=hdinc g N hg hNL
    rw[hNeR] at ht
    simpa only[show 2*(3*(g:ℝ))=6*(g:ℝ) by ring] using ht
  have hconst:|4*Real.log (g:ℝ)+4|≤(4+4/Real.log 2)*Real.log ((g:ℝ)+1):=by
    have hlogg:0≤Real.log (g:ℝ):=Real.log_nonneg hgr
    have hlogle:Real.log (g:ℝ)≤Real.log ((g:ℝ)+1):=Real.log_le_log hgR (by linarith)
    have hloglow:Real.log 2≤Real.log ((g:ℝ)+1):=Real.log_le_log (by norm_num) (by linarith)
    have ht:=mul_le_mul_of_nonneg_left hloglow (show 0≤4/Real.log 2 by positivity)
    have he:4/Real.log 2*Real.log 2=4:=by field_simp
    rw[he] at ht
    rw[abs_of_nonneg (by positivity:0≤4*Real.log (g:ℝ)+4)]
    nlinarith
  have hprof: (g:ℝ)*logDegreeProfile ((k:ℝ)/g)=
      unscaledSaddleAction (2*(g:ℝ)) (3*(g:ℝ)-k)+(3*(g:ℝ)-k)*Real.log (3*(g:ℝ)-k)+
        (3*(g:ℝ))*Real.log (6*(g:ℝ))-(k:ℝ)*Real.log (2*(k:ℝ))-
          2*(3*(g:ℝ)-k)*Real.log (g:ℝ)-2*(3*(g:ℝ)-k):=
    (degree_profile_exact_scaled_action g k hgR (Nat.cast_nonneg k) (by exact_mod_cast hkL)).symm
  have hid:Real.log (oneBoundaryModelJ g k/(oneBoundaryModelJ g N*(g:ℝ)^(2*m)))-
      (g:ℝ)*logDegreeProfile ((k:ℝ)/g)=
      (Real.log (m.factorial:ℝ)-((m:ℝ)*Real.log m-m))+
        (Real.log (unscaledCoeff h m)-unscaledSaddleAction h m)+
        (Real.log (oddFactorial N:ℝ)-((N:ℝ)*Real.log (2*(N:ℝ))-N))-
        (Real.log (oddFactorial k:ℝ)-((k:ℝ)*Real.log (2*(k:ℝ))-k))-
        (unscaledSaddleAction (2*(g:ℝ)) (3*(g:ℝ)-k)-unscaledSaddleAction h m)-
        ((3*(g:ℝ)-k)*Real.log (3*(g:ℝ)-k)-(m:ℝ)*Real.log m)-
        ((3*(g:ℝ))*Real.log (6*(g:ℝ))-(N:ℝ)*Real.log (2*(N:ℝ)))+
        (4*Real.log (g:ℝ)+4):=by
    rw[oneBoundaryModelJ_log_quotient g k hg hk,hprof]
    change Real.log (m.factorial:ℝ)+Real.log (unscaledCoeff h m)+Real.log (oddFactorial N:ℝ)-
      Real.log (oddFactorial k:ℝ)-(2*m:ℕ)*Real.log (g:ℝ)-_=_
    push_cast
    rw[←hmeR,←hmk]
    ring
  change |Real.log (oneBoundaryModelJ g k/(oneBoundaryModelJ g N*(g:ℝ)^(2*m)))-
      (g:ℝ)*logDegreeProfile ((k:ℝ)/g)|≤_
  rw[hid]
  obtain ⟨hF1,hF2⟩:=abs_le.mp hF
  obtain ⟨hS1,hS2⟩:=abs_le.mp hS
  obtain ⟨hO1,hO2⟩:=abs_le.mp hO
  obtain ⟨hK1,hK2⟩:=abs_le.mp hK
  obtain ⟨hT1,hT2⟩:=abs_le.mp hT
  obtain ⟨hX1,hX2⟩:=abs_le.mp hX
  obtain ⟨hD1,hD2⟩:=abs_le.mp hD
  obtain ⟨hc1,hc2⟩:=abs_le.mp hconst
  dsimp[C]
  apply abs_le.mpr
  constructor <;>nlinarith only[hF1,hF2,hS1,hS2,hO1,hO2,hK1,hK2,hT1,hT2,hX1,hX2,hD1,hD2,hc1,hc2]
end WP.Coefficients
