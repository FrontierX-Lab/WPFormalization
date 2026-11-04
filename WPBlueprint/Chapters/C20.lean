import WPFormalization.Statements
import WPBlueprint.Chapters.C19
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "appE-adjacent-rate" =>

# The rate for adjacent coefficient ratios

This appendix proves Theorem {bpref "thm:quantitative-coefficient"}[E.1], which contains the rate in Theorem {bpref "thm:coefficient"}[1.4]. We quantify the three degree ranges treated in Section 13. The logarithmic comparison and concavity give the rate away from the lowest degrees, including bounded positive codimension at the top. Bracket difference estimates supply the remaining range. Balancing the bounds gives $`O(g^{-1/8})` uniformly; we do not claim that this exponent is optimal. The coefficients and the exact density are those of Theorem {bpref "thm:coefficient"}[1.4].

:::theorem "thm:quantitative-coefficient" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H5")
%%%
source := { document := "paper-v3", spans := #[{ page := "97", anchor := "thm:quantitative-coefficient", citation := "Theorem E.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Theorem E.1 — Quantitative adjacent ratios.

There is a constant $`C` such that, for all sufficiently large $`g`, 

$$`\sup_{0\le k<3g-2}
 \left|\frac{a_{g,k}/a_{g,k+1}}{4\pi^2/t_{g,k}^2}-1\right|
 \le Cg^{-1/8}.`

 For every fixed $`\varepsilon\in(0,3)` there is $`C_\varepsilon` such that 

$$`\sup_{\varepsilon g\le k<3g-2}
 \left|\frac{a_{g,k}/a_{g,k+1}}{4\pi^2/t_{g,k}^2}-1\right|
 \le C_\varepsilon g^{-1/4}.`

 In the second supremum $`k` is an integer. Both bounds include bounded positive codimension from the top coefficient.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



## The logarithmic model up to its endpoints

We first make the logarithmic comparison of Section 13 quantitative, up to both ends of the degree range.

Use $`H,\widetilde A_m,\mu` from 13.4 and 13.10. Let $`\zeta(u)` be the inverse of $`\mu(z)` on $`0\le u\le3/2`, with $`\zeta(0)=0`. Since $`\mu(z)=z/5+O(z^2)` at zero and $`\mu'(z)>0` throughout $`[0,\pi^2/2]`, the function 

$$`\chi(u)=u/\zeta(u),\qquad \chi(0)=1/5,`

 is positive and analytic in a neighborhood of the closed real interval. Write $`f` for the function in 13.14, extended continuously to $`[0,3]`, and set 

$$`\mathfrak q(\alpha)=4\alpha\chi((3-\alpha)/2),\qquad
 f'(\alpha)=-\log\mathfrak q(\alpha),\qquad
 |f''(\alpha)|\le C(1+\alpha^{-1})\quad(0<\alpha\le3).`

 These follow from 13.15; in particular $`\mathfrak q(3)=12/5` and $`f(3)=0`.

We need the endpoint-uniform version of the logarithmic saddle estimate 13.12.

:::lemma_ "lem:uniform-saddle" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H12")
%%%
source := { document := "paper-v3", spans := #[{ page := "98", anchor := "lem:uniform-saddle", citation := "Lemma E.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma E.2 — Endpoint-uniform saddle estimate.

For integers $`0\le m\le3h/2`, let $`z=\zeta(m/h)`, interpreting the $`m=0` expressions by continuity. Then, uniformly in $`m`, 

$$`\log \widetilde A_m(h)=-h\log H(z)-m\log z+O(\log(h+1)).`


:::



:::proof "lem:uniform-saddle" (uses := "lem:kernel-positivity")
Tilt $`H^{-1}` at $`z` and let $`S_h` be the sum of $`h` independent variables with probability generating function $`H(z)/H(zw)`. Exactly, 

$$`\widetilde A_m(h)=H(z)^{-h}z^{-m}\Pr(S_h=m).`

 There is $`c>0` such that $`\Pr(S_h=m)\ge c/\sqrt{m+1}` uniformly. We give the details at the degenerate endpoint $`m/h\to0`. When $`m\to\infty` and $`m/h\to0`, one has $`z\asymp m/h`, $`\operatorname{Var}(S_h)\asymp m`, and each fixed cumulant of the sum is $`O(m)`. The probabilities at zero and one of one summand have product comparable to $`z`. The Fourier bound 9.8 therefore gives $`\exp(-cm\theta^2)` on $`[-\pi,\pi]`, and the centered Taylor expansion gives the local Gaussian limit at $`m`, with central mass asymptotic to $`(2\pi\operatorname{Var}(S_h))^{-1/2}`. When $`m/h` stays away from zero, the same argument uses a compact tilted family with variance comparable to $`h` and positive zero and one probabilities. If $`m` stays bounded, pass to a fixed integer $`m`; then $`z=5m/h+O_m(h^{-2})` and $`\widetilde A_m(h)=(h/5)^m/m!\,(1+O_m(h^{-1}))`, so the central mass tends to $`\mathrm{e}^{-m}m^m/m!>0`. At $`m=0` it is one. These cases and a subsequence contradiction prove the asserted uniform lower bound. The upper bound is one, proving E.4.
:::



Put 

$$`G_g(k)=\log\frac{J_k}{J_Ng^{2(N-k)}},\qquad N=3g-2.`



:::lemma_ "lem:log-comparison" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H5")
%%%
source := { document := "paper-v3", spans := #[{ page := "98", anchor := "lem:log-comparison", citation := "Lemma E.3", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma E.3 — Logarithmic comparison up to the endpoints.

There is a constant $`C` such that 

$$`\max_{0\le k\le N}|G_g(k)-g f(k/g)|\le C\sqrt g.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



:::proof "lem:log-comparison" (uses := "prop:harmonic, lem:uniform-saddle, ext:stirling")
This follows from the model 13.4, the comparison 13.5 and Lemma {bpref "lem:uniform-saddle"}[E.2]. The passage to $`f` is uniform, even at $`m=0`. To see this, use the exact model for the intersection number, $`3^h\Gamma(h)4^{-g}m!\widetilde A_m(h)/(2k+1)!!` from Section 13 and apply Stirling’s bound with logarithmic error to its factorials, using $`0\log0=0`. Replacing $`h=2g-1` by $`2g` and $`m=3g-2-k` by $`3g-k` changes its saddle action by $`O(\log(g+1))`: the two partial derivatives of the action are $`-\log H(z)` and $`-\log z`, the latter having only an integrable logarithmic singularity at $`m=0`. The powers of $`g` cancel as in 13.13–13.14. Subtracting the top model value gives $`g f(k/g)+O(\log(g+1))` uniformly. The two logarithmic errors between the true and the model values are at most $`C\sqrt g` by 13.5, including the top coefficient, which proves E.5.
:::



## Quantitative secants and the top endpoint

:::proof "thm:quantitative-coefficient" (uses := "lem:log-comparison, eq:C7, eq:C8, eq:C18, eq:C23")
The sequence $`G_g` is concave by {bpref "eq:C7"}[13.7]. Write $`q_k=J_k/J_{k+1}`. For an integer $`\ell\ge1` with $`\ell\le k/2` and $`k+\ell\le N`, its secants imply 

$$`-\frac{G_g(k)-G_g(k-\ell)}\ell
 \le\log(q_k/g^2)
 \le-\frac{G_g(k+\ell)-G_g(k)}\ell.`

 Equations E.3 and E.5 yield 

$$`\left|\log\frac{q_k}{g^2\mathfrak q(k/g)}\right|
 \le C\left(\frac{\sqrt g}\ell+\frac\ell k\right).`

 If $`k+\ell>N`, retain the lower secant and use $`q_k\le q_{N-1}` for the upper bound. The exact top anchor {bpref "eq:C18"}[13.18] gives $`q_{N-1}/g^2=12/5+O(g^{-1})`. Since $`\log\mathfrak q` is Lipschitz near three and $`3-k/g\le(\ell+2)/g`, this gives the same bound E.6, with a changed constant.

Take $`\ell=\lfloor g^{5/8}\rfloor`. For $`k\ge g^{3/4}` it is at most $`k/2` for large $`g`, and E.6 is $`O(g^{-1/8})`. For $`k\ge\varepsilon g`, instead take $`\ell=\lfloor g^{3/4}\rfloor` to obtain $`O_\varepsilon(g^{-1/4})`.

These estimates for the intersection numbers translate into the statement of the theorem without losing the bounded-codimension range. Indeed, put $`m=N-k`, $`h=2g-1`, and $`z_{g,k}=t_{g,k}^2/2`. By 13.11, $`\mu(z_{g,k})=m/h`. Therefore the value of $`q_k=J_k/J_{k+1}` that corresponds, through 13.3, to the proposed equivalent $`4\pi^2/t_{g,k}^2` of $`a_{g,k}/a_{g,k+1}` is 

$$`\frac{(2k+3)m}{z_{g,k}}
 =(2k+3)h\chi(m/h)
 =g^2\mathfrak q(k/g)\left(1+O(k^{-1}+g^{-1})\right).`

 The last error is uniform for $`k\ge1`: the two arguments of $`\chi` differ by $`O(g^{-1})`, while $`\chi` is positive with bounded logarithmic derivative on the closed interval. This calculation retains $`m` exactly, including $`m=1`. By 13.3, the two secant estimates prove E.1 for $`k\ge g^{3/4}` and all of E.2.

The small-degree range.

It remains to consider $`k\le g^{3/4}`. Put $`\rho_k=b_{g,k}/b_{g,k+1}\ge1` and $`\omega_k=(2k+3)(N-k)` as before. Equation 13.25 gives $`\rho_k=1+O(g^{-1/2})` for $`k\le\delta_0\sqrt g` with a fixed small $`\delta_0>0`. For the remaining indices we claim 

$$`0\le\rho_k-1\le C\left(
       \frac{\log(g+1)}{\sqrt k}+\sqrt{\frac kg}+\frac1k\right)
 \quad(\delta_0\sqrt g\le k\le g^{3/4}).`

 First $`\rho_k<2` uniformly in this range for large $`g`. Otherwise monotonicity of $`q_j` and $`\omega_j/\omega_k\le1+\delta` propagate a fixed ratio gap over a block of length comparable to $`k`. Its product would force $`\log(V_{g,1}/b_{g,j})\ge c k` at an index $`j\asymp k`, contradicting {bpref "eq:C23"}[13.23], whose upper bound is $`o(k)` uniformly on this range.

Now put $`\eta=\rho_k-1\in[0,1]` and $`\delta=\eta/6`. For $`k\le j\le\lfloor(1+\delta)k\rfloor`, the same monotonicity and the exact factor $`\omega_j` give $`\rho_j\ge(1+\eta)/(1+\delta)\ge1+\eta/2`. If $`\eta k\ge12`, this block has at least $`\eta k/12` indices. Summing logarithms over the block and using {bpref "eq:C23"}[13.23] at its last index plus one gives 

$$`c\eta^2 k\le C\log^2(g+1)+Ck^2/g.`

 All these indices lie below the fixed $`c_0g` range of {bpref "eq:C23"}[13.23] for large $`g`. If $`\eta k<12`, then $`\eta<12/k` directly. This proves E.8. Its right side is $`O(g^{-1/8})` on the displayed range. Thus $`\rho_k=1+O(g^{-1/8})` uniformly for $`0\le k\le g^{3/4}`.

Finally the saddle equation at $`t=\pi` gives $`\pi^2/t_{g,k}^2=1+O((k+1)/g)` uniformly on this small-degree range. Since $`a_{g,k}/a_{g,k+1}=4\rho_k`, the desired relative error is $`O(g^{-1/8})` there as well. Together with the secant range this proves both assertions.
:::



The argument is a quantitative version of the one used for the leading equivalent, based on the same logarithmic comparison and concavity. Liu–Xu’s fixed-codimension expansion has finer errors at each fixed codimension \[55\]; the bounds here hold with a single constant across all valid degrees.
