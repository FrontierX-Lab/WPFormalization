import WPFormalization.HigherOrder.LinearGeometricBudget
/-! Positive four-stage induction with common exponential constants.
Rows 0/1/2/3 represent the profile, cusp, higher-marking genus, and one-marking genus stages.
The actual analytic steps must supply all four hypotheses. No actual remainder assertion or external input is introduced here. -/

noncomputable section
namespace WP.HigherOrder
lemma four_stage_predicate_geometric_closure
    (U:Fin 4→ℕ→ℝ→Prop) (b F B K F₁:ℝ)
    (hb:0 ≤ b) (hF:0 ≤ F) (hB:0<B) (hK:0 ≤ K) (hF₁:0 ≤ F₁)
    (hmono:∀s n,Monotone (U s n)) (hbase:∀s,U s 1 F₁)
    (hprofile:∀n:ℕ,2 ≤ n→∀e:ℕ→ℝ,(∀m,0 ≤ e m)→
      (∀m:ℕ,1 ≤ m→m<n→∀s,U s m (e m))→
      U 0 n (F*B^n+∑i∈Finset.Icc 1 n,K*B^i*e (n-i)))
    (hcusp:∀n:ℕ,2 ≤ n→∀E:ℝ,0 ≤ E→U 0 n E→U 1 n (F*B^n+b*E))
    (hhigh:∀n:ℕ,2 ≤ n→∀e:ℕ→ℝ,(∀m,0 ≤ e m)→
      (∀m:ℕ,1 ≤ m→m<n→∀s,U s m (e m))→
      ∀E:ℝ,0 ≤ E→U 0 n E→
      U 2 n (F*B^n+b*E+∑i∈Finset.Icc 1 n,K*B^i*e (n-i)))
    (hlow:∀n:ℕ,2 ≤ n→∀e:ℕ→ℝ,(∀m,0 ≤ e m)→
      (∀m:ℕ,1 ≤ m→m<n→∀s,U s m (e m))→
      ∀C H:ℝ,0 ≤ C→0 ≤ H→U 1 n C→U 2 n H→
      U 3 n (F*B^n+b*(H+C)+∑i∈Finset.Icc 1 n,K*B^i*e (n-i))) :
    ∃C Q:ℝ,0<C ∧ 0<Q ∧∀n:ℕ,1 ≤ n→∀s,U s n (C*Q^n) := by
  let A:ℝ:=4+4*b+2*b^2
  have hA:0 ≤ A:=by dsimp[A];positivity
  let Q:ℝ:=4*(A*(3*K)+1)*B
  have hQ:0<Q:=by dsimp[Q];positivity
  have hAK:0 ≤ A*(3*K):=by positivity
  have hBq:2*B ≤ Q:=by dsimp[Q];nlinarith[mul_nonneg hAK hB.le]
  have hres:12*A*K*B ≤ Q:=by dsimp[Q];nlinarith
  let C:ℝ:=2*A*F+F₁/Q+1
  have hC:0<C:=by dsimp[C];positivity
  have hforce:2*A*F ≤ C:=by dsimp[C];linarith[div_nonneg hF₁ hQ.le]
  have hinit:F₁ ≤ C*Q:=by
    have hh:F₁/Q ≤ C:=by dsimp[C];linarith[mul_nonneg hA hF]
    have hh':=mul_le_mul_of_nonneg_right hh hQ.le
    simpa only[div_mul_cancel₀ _ hQ.ne'] using hh'
  refine ⟨C,Q,hC,hQ,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih=>
    intro hn
    by_cases hn1:n=1
    · subst n
      intro s
      exact hmono s 1 (by simpa only[pow_one] using hinit) (hbase s)
    have hn2:2 ≤ n:=by omega
    let e:ℕ→ℝ:=fun m=>C*Q^m
    have he:∀m,0 ≤ e m:=by intro m;dsimp[e];positivity
    have hprev:∀m:ℕ,1 ≤ m→m<n→∀s,U s m (e m):=by
      intro m hm hmn
      exact ih m hmn hm
    let T:ℝ:=∑i∈Finset.Icc 1 n,K*B^i*e (n-i)
    have hT:0 ≤ T:=Finset.sum_nonneg (fun i hi=>by have hh:=he (n-i);positivity)
    let E:=F*B^n+T
    let Cₙ:=F*B^n+b*E
    let H:=F*B^n+b*E+T
    let G:=F*B^n+b*(H+Cₙ)+T
    have hE0:0 ≤ E:=by dsimp[E];positivity
    have hC0:0 ≤ Cₙ:=by dsimp[Cₙ];positivity
    have hH0:0 ≤ H:=by dsimp[H];positivity
    have hG0:0 ≤ G:=by dsimp[G];positivity
    have hE:U 0 n E:=hprofile n hn2 e he hprev
    have hCₙ:U 1 n Cₙ:=hcusp n hn2 E hE0 hE
    have hH:U 2 n H:=hhigh n hn2 e he hprev E hE0 hE
    have hG:U 3 n G:=hlow n hn2 e he hprev Cₙ H hC0 hH0 hCₙ hH
    have htotal:E+Cₙ+H+G ≤ C*Q^n:=by
      apply four_stage_geometric_budget b F B K C Q n hb hF hB hK hC.le hQ hBq hres hforce E Cₙ H G
        le_rfl le_rfl le_rfl le_rfl
    intro s
    fin_cases s
    · exact hmono 0 n (by linarith) hE
    · exact hmono 1 n (by linarith) hCₙ
    · exact hmono 2 n (by linarith) hH
    · exact hmono 3 n (by linarith) hG
end WP.HigherOrder
