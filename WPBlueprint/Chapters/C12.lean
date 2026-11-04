import WPFormalization.Statements
import WPBlueprint.Chapters.C11
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "13-coefficients" =>

# Uniform one-boundary coefficient ratios

The coefficient problem uses the same harmonic comparison, but not the higher-order marked expansion. Log-concavity converts the logarithmic comparison into adjacent ratios in the interior. Near the top degree we use an exact intersection number; near degree zero we use bracket difference estimates. We first prove the uniform equivalent and then, in Appendix E, quantify its error.

Put $`N=3g-2` and retain the defining normalization 

$$`V_{g,1}(L)=\sum_{k=0}^{N}\frac{a_{g,k}}{(2k+1)!}L^{2k},
 \qquad b_{g,k}=[\tau_k]_{g,1}=4^k a_{g,k}.`

 For every valid adjacent index $`0\le k<N`, define $`t_{g,k}\in(0,\pi)` by

:::definition "eq:C1" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "def:stable")
%%%
source := { document := "paper-v3", spans := #[{ page := "52", anchor := "eq:C1", citation := "Equation 13.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 13.1 — Exact-density trigonometric saddle.

In the setup and notation of this section, the paper defines or asserts:



$$`\alpha_{g,k}:=\frac{2k+1}{2g-1}
 =\frac{t_{g,k}^{2}\sin t_{g,k}}
        {\sin t_{g,k}-t_{g,k}\cos t_{g,k}}.`


:::



The assertion to prove is 

$$`\sup_{0\le k<3g-2}
 \left|\frac{a_{g,k}/a_{g,k+1}}{4\pi^2/t_{g,k}^{2}}-1\right|
 \longrightarrow0.`

 Equivalently, the comparison for $`b_{g,k}/b_{g,k+1}` is $`\pi^2/t_{g,k}^2`. The ratio at $`k=N` is undefined and is not included. In the boundary-length normalization of $`V_{g,1}(L)`, the bottom limit is four, while the top adjacent ratios diverge.

## Coefficient identities and further inputs

We first prove the uniform equivalent 13.2; Appendix E supplies the quantitative error in Theorem {bpref "thm:coefficient"}[1.4]. Let 

$$`J_k=\int_{\overline{\mathcal M}_{g,1}}
       \kappa_1^{N-k}\psi_1^k,
 \qquad m=N-k,\quad h=2g-1.`

 The exact coefficient identities are 

$$`a_{g,k}=(2k+1)!!\frac{(2\pi^2)^m}{m!}J_k,
 \qquad
 \frac{a_{g,k}}{a_{g,k+1}}
 =\frac{2\pi^2}{(2k+3)(N-k)}\frac{J_k}{J_{k+1}}.`

 Note that $`J_k` is a mixed $`\kappa_1`–$`\psi_1` intersection number, not a pure $`\psi` intersection number.

We use the following consequences of Section 5. Define 

$$`H(z)=\frac{3(\sin t-t\cos t)}{t^3},\quad t=\sqrt{2z},
 \qquad \widetilde A_m(h)=[z^m]H(z)^{-h},`

 with the removable value $`H(0)=1`, and 

$$`M_{g,k}=4^k\frac{3^h\Gamma(h)}{4^g}
                  (2\pi^2)^m \widetilde A_m(h).`

 Thus $`H=H_0` is the kernel of Section 2 at $`Y=0`. The tilde indicates that $`\widetilde A_m(h)` is a coefficient of the unscaled kernel $`H_0`; thus $`\widetilde A_m(h)=r_0^{-m}A_m(h)`, with $`A_m(h)` from {bpref "eq:H12"}[4.11] at $`Y=0` and $`r_0=\pi^2/2`. There is an absolute $`C` such that, for every sufficiently large $`g`, uniformly in $`0\le k\le N`, 

$$`\exp[-C\log^2(g+1)]
 \le\frac{b_{g,k}}{M_{g,k}}
 \le\exp(C\sqrt g).`

 This is the case of one marking of 5.20–5.22. At $`Y=0`, the unscaled amplitude is $`U^0=b/[4^k(2\pi^2)^m]`; undoing that scaling gives exactly 13.4, without an additional genus-dependent factor. In particular 

$$`\sup_{0\le k\le N}\frac1g
       \left|\log\frac{b_{g,k}}{M_{g,k}}\right|\longrightarrow0.`

 The lower estimate in 13.5 will also control the bottom endpoint.

We also use the following three facts, which are independent of the harmonic comparison.

1. The cotangent classes are nef on the compactification. Indeed, the nef logarithmic relative dualizing class in \[49\] Theorem 0.4 is the cotangent class at the additional mark under the identification of the universal curve with the moduli space with one additional mark. The logarithmic kappa class is nef as well: for the forgetful universal curve $`\pi:\overline{\mathcal M}_{g,n+1}\to\overline{\mathcal M}_{g,n}`, one has $`\kappa_1=\pi_*(\psi_{n+1}^2)` \[8\]. Its intersection against any complete curve is the square of the pulled-back nef cotangent class on the pulled-back universal surface, and hence is nonnegative. This argument can be carried out after a finite cover supporting a family and on its projective coarse surface; passage to the coarse space multiplies all mixed intersection numbers by the same positive factor and does not affect the inequality. Thus the nef rational divisor classes on the projective coarse moduli space satisfy the Khovanskii–Teissier inequalities \[52\] Section 1.6; see also \[10\] Theorem 2.15. This gives
:::proposition "eq:C7" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H5")
%%%
source := { document := "paper-v3", spans := #[{ page := "53", anchor := "eq:C7", citation := "Equation 13.7", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 13.7 — Log concavity of unnormalized mixed intersections.

In the setup and notation of this section, the paper defines or asserts:



$$`J_k^2\ge J_{k-1}J_{k+1},\qquad 1\le k<N.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::


   Thus $`q_k:=J_k/J_{k+1}` is nondecreasing. No log-concavity of the normalized bracket sequence is assumed.

2. Bracket monotonicity and the fixed-marking absolute difference estimate of Mirzakhani–Zograf \[66\] Theorem 3.2(ii) give, with $`c_k=b_{g,k}/V_{g,1}`,
:::proposition "eq:C8" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H5")
%%%
source := { document := "paper-v3", spans := #[{ page := "53", anchor := "eq:C8", citation := "Equation 13.8", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 13.8 — Absolute bracket differences.

In the setup and notation of this section, the paper defines or asserts:



$$`c_0=1,\qquad 0\le c_k-c_{k+1}\le C\frac{k+1}{g},
  \qquad 0\le k<N.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::


   For $`k\ge1`, their explicit bound is $`b_{g,k}-b_{g,k+1}\le16((k+1)V_{g,0}+kV_{g-1,2})`; the fixed-marking volume ratios turn it into {bpref "eq:C8"}[13.8]. The $`k=0` case is the fixed-degree estimate $`1-c_1=O(1/g)`. Summing {bpref "eq:C8"}[13.8] gives $`1-c_k\le Ck(k+1)/g`. These are absolute estimates, so they cannot be divided by an arbitrarily small $`c_k`.

3. The fixed-marking leading volume asymptotic gives 
   $$`V_{g,1}\asymp g^{-1/2}\Gamma(2g-1)
                      (4\pi^2)^{2g-2},`
    and the one-point pure-$`\psi` identity is $`J_N=1/(24^g g!)`. Only the upper bound in 13.9 is needed below. The exact value of the top ratio is derived below from the ordinary DVV and string equations.

## The saddle equation for the degree

The reciprocal of $`H` has strictly positive Taylor coefficients and is analytic on a neighborhood of $`[0,\pi^2/2]`. These facts also follow directly from $`2zH''+5H'+H=0`: writing $`-H'/H=\sum_{j\ge0}r_jz^j` gives $`r_0=1/5` and 

$$`(2j+5)r_j=2\sum_{u+v=j-1}r_ur_v>0\quad(j\ge1).`

 Hence $`-\log H` and $`H^{-1}` have positive nonconstant coefficients. There is no positive real zero of $`H` through $`\pi^2/2`, because $`\sin t-t\cos t>0` for $`0<t\le\pi`; by Pringsheim’s theorem this excludes a smaller complex singularity of $`H^{-1}`.

For $`0<z\le\pi^2/2`, tilt these coefficients to a probability law with generating function $`H(z)/H(zw)`. Its mean is 

$$`\mu(z)=-\frac{zH'(z)}{H(z)}
 =\frac12\left(3-
     \frac{t^2\sin t}{\sin t-t\cos t}\right),
 \qquad t=\sqrt{2z}.`

 Its variance is $`z\mu'(z)>0`. Thus the right side of {bpref "eq:C1"}[13.1], as a function of $`t`, decreases strictly from three to zero on $`(0,\pi)`, proving existence and uniqueness in {bpref "eq:C1"}[13.1]. Notice the exact dimension identity 

$$`\frac mh=\frac{3-\alpha_{g,k}}2,
 \qquad \alpha_{g,k}=3-\frac{2m}{h}.`



For $`m/h` in a compact subset of $`(0,3/2)`, there is a unique saddle $`z` with $`\mu(z)=m/h`. Fourier inversion for the tilted iid sum, whose laws have uniform exponential moments and positive probabilities at zero and one, gives 

$$`\log \widetilde A_m(h)=-h\log H(z)-m\log z+O(\log h).`

 The error is uniform on such compact subsets.

## Interior degrees: exponential comparison and concavity

Suppose $`k/g\to\alpha\in(0,3)` and let $`z=t^2/2` solve $`\mu(z)=(3-\alpha)/2`. Interpolate linearly on the degree mesh the values 

$$`f_g(k/g)=\frac1g\log
               \frac{J_k}{J_Ng^{2(N-k)}}.`

 By {bpref "eq:C7"}[13.7], these functions are concave. Equations 13.3–13.6, 13.12, and Stirling’s formula give their pointwise limit on $`(0,3)`: 

$$`\begin{aligned}
 f(\alpha)={}&-2\log H(z)-(3-\alpha)\log z
 +(3-\alpha)\log(3-\alpha)\\
 &+3\log6-\alpha\log(2\alpha)-2(3-\alpha).
 \end{aligned}`

 Explicitly, the model for the intersection number $`J_k` is $`J_k^{\mathrm{mod}}=3^h\Gamma(h)4^{-g}m!\widetilde A_m(h)/(2k+1)!!`. Its quotient by the top model value is exactly $`m! \widetilde A_m(h)(2N+1)!!/(2k+1)!!`; the two occurrences of $`(N-k)\log g` in its Stirling expansion cancel the affine normalization in 13.13. The logarithmic errors in 13.6, including the top one, vanish after division by $`g`.

Differentiation of 13.14 gives 

$$`f'(\alpha)=\log\frac{z}{2\alpha(3-\alpha)}.`

 The terms containing $`dz/d\alpha` cancel by the saddle equation. Concavity now upgrades the exponential-scale information to an adjacent ratio. For fixed small $`\varepsilon>0`, the slope on $`[k/g,(k+1)/g]` is at most the secant slope on $`[\alpha-2\varepsilon,\alpha-\varepsilon]` and at least the one on $`[\alpha+\varepsilon,\alpha+2\varepsilon]`, for all sufficiently large $`g`. These four endpoints are fixed, so pointwise convergence suffices. First let $`g` tend to infinity and then let $`\varepsilon` decrease to zero. Since 13.14 is differentiable, the neighboring slope converges to 13.15. Consequently 

$$`\frac{J_k}{g^2J_{k+1}}\longrightarrow
            \frac{2\alpha(3-\alpha)}z.`

 Using the exact identity 13.3, 

$$`\frac{a_{g,k}}{a_{g,k+1}}\longrightarrow
      \frac{2\pi^2}{z}=\frac{4\pi^2}{t^2}.`

 The passage from macroscopic secants to adjacent ratios uses the concavity of $`\log J_k`.

## The top endpoint, including bounded codimension

The one-kappa pushforward identity gives $`J_{N-1}=\langle\tau_2\tau_{3g-3}\rangle_g`. Applying DVV at the degree-two insertion and then the string equation twice gives 

$$`15J_{N-1}=
 \{(6g-3)(6g-5)+12g\}J_N.`

 The nonseparating term is $`(1/2)\langle\tau_0^2\tau_{3g-3}\rangle_{g-1}=12gJ_N`; separating terms vanish by dimension. At $`g=1`, the same identity follows directly from $`\langle\tau_0^3\rangle_0=1`. Therefore

:::proposition "eq:C18" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H5")
%%%
source := { document := "paper-v3", spans := #[{ page := "55", anchor := "eq:C18", citation := "Equation 13.18", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 13.18 — Exact top adjacent coefficient anchor.

In the setup and notation of this section, the paper defines or asserts:



$$`q_{N-1}=\frac{12g^2-12g+5}{5},
 \qquad
 \frac{a_{g,N-1}}{a_{g,N}}
 =\frac{2\pi^2(12g^2-12g+5)}{5(6g-3)}.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



Let $`m=N-k\ge1` and $`m=o(g)`. For each fixed $`\alpha<3`, eventually $`q_{\lfloor\alpha g\rfloor}\le q_{N-m}\le q_{N-1}` by {bpref "eq:C7"}[13.7]. As $`\alpha` increases to three, the limit on the right side of 13.16 tends to $`12/5`, because 

$$`\frac{t^2\sin t}{\sin t-t\cos t}
       =3-\frac{t^2}{5}+O(t^4)\quad(t\to0).`

 The exact top value {bpref "eq:C18"}[13.18] gives the same limit. Hence 

$$`\frac{q_{N-m}}{g^2}\longrightarrow\frac{12}{5},
 \qquad
 \frac{a_{g,N-m}}{a_{g,N-m+1}}
       \sim\frac{4\pi^2g}{5m}\quad(m=o(g),\ m\ge1).`

 In particular the statement includes every fixed positive codimension. For fixed $`m`, this leading term agrees, after the length normalization above, with the fixed-codimension expansion of Liu–Xu \[55\] Theorem 1.2. The same monotonicity argument also covers unbounded $`m=o(g)` and joins this endpoint to the interior limit.

## The lowest degrees

Near degree zero the interior argument gives no information: the comparison 13.5 determines $`\log b_{g,k}` only up to an error $`o(g)`, whereas for $`k=o(g)` the quantities to be determined vary on a smaller scale. We combine two other inputs. For degrees up to a power of $`\log g`, the absolute estimate {bpref "eq:C8"}[13.8] of Mirzakhani and Zograf gives the ratios directly. For larger $`k=o(g)`, we argue by contradiction: by the monotonicity of the ratios $`q_k`, a ratio bounded away from one would persist over a range of degrees comparable to $`k`, and would force $`b_{g,k}` to drop below the lower bound {bpref "eq:C23"}[13.23].

Set $`z_0=\pi^2/2`, and let $`S_h` be the sum of $`h` iid variables with generating function $`H(z_0)/H(z_0w)`. Since $`H(z_0)=3/\pi^2`, 13.4 becomes the exact identity 

$$`M_{g,k}=\pi^2\Gamma(h)(4\pi^2)^{h-1}
                     \Pr(S_h=N-k).`

 The summands have mean $`3/2`, nonzero variance, span one, and exponential moments. Uniform exponential tilting in a fixed neighborhood of that mean gives, for $`0\le k\le c_0g` with one fixed small $`c_0>0`, 

$$`\Pr(S_h=N-k)\ge c g^{-1/2}
            \exp[-C(k+1)^2/g].`

 Indeed the tilted local central limit estimate gives the factor $`g^{-1/2}`, while the rate function has a quadratic zero at the mean; the displacement here is exactly $`k+1/2`. Combining 13.5, 13.9, and 13.21–13.22 yields

:::proposition "eq:C23" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H5")
%%%
source := { document := "paper-v3", spans := #[{ page := "55", anchor := "eq:C23", citation := "Equation 13.23", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 13.23 — Bottom-degree logarithmic bound.

In the setup and notation of this section, the paper defines or asserts:



$$`0\le\log\frac{V_{g,1}}{b_{g,k}}
 \le C\log^2(g+1)+C\frac{(k+1)^2}{g}.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



Write 

$$`\rho_k=\frac{b_{g,k}}{b_{g,k+1}}\ge1,
 \qquad \omega_k=(2k+3)(N-k),
 \qquad \rho_k=\frac{\pi^2q_k}{2\omega_k}.`

 Suppose $`k=o(g)` but, along a subsequence, $`\rho_k\ge1+\eta` for a fixed $`\eta>0`. First consider $`k>\log^3(g+1)`; then {bpref "eq:C23"}[13.23] is $`o(k)` at every index comparable to $`k`. Put $`\delta=\eta/[2(2+\eta)]`. For $`k\le j\le\lfloor(1+\delta)k\rfloor`, 

$$`\frac{\omega_j}{\omega_k}\le\frac{2j+3}{2k+3}\le1+\delta,
 \qquad
 \rho_j\ge\rho_k\frac{\omega_k}{\omega_j}
            \ge1+\eta/2.`

 These inequalities follow from the monotonicity of the raw ratios $`q_j`. Multiplying these inequalities forces $`\log(V_{g,1}/b_{g,\lfloor(1+\delta)k\rfloor+1})\ge c_\eta k`, contradicting {bpref "eq:C23"}[13.23].

For the remaining indices $`k\le\log^3(g+1)`, summing the absolute estimate {bpref "eq:C8"}[13.8] gives $`c_{k+1}=1-o(1)` uniformly, so division in {bpref "eq:C8"}[13.8] is legitimate. In fact there is a fixed small $`\delta_0>0` for which 

$$`\rho_k=1+O((k+1)/g)
       \quad(0\le k\le\delta_0\sqrt g).`

 This proves 

$$`\frac{a_{g,k}}{a_{g,k+1}}\longrightarrow4
                  \quad\text{whenever }k=o(g).`

 No positive lower bound on $`c_k` was assumed outside the small square-root window.

## Combining the degree ranges

Proof discussion. Take any sequence of valid indices and a subsequence on which $`k/g` converges in $`[0,3]`. An interior limit is covered by 13.17, and a zero limit by 13.26, while the comparison in {bpref "eq:C1"}[13.1] also tends to four. If the limit is three, then $`m=N-k=o(g)` and 13.20 applies. Equations 13.11 and 13.19 give 

$$`t_{g,k}^2\sim\frac{10m}{2g-1},\qquad
 \frac{4\pi^2}{t_{g,k}^2}\sim\frac{4\pi^2g}{5m}.`

 Thus the true and the proposed ratios are asymptotically equal on that subsequence too. A sequence violating the supremum statement 13.2 would contradict one of these three cases.



The effective density $`(2k+1)/(2g-1)` in {bpref "eq:C1"}[13.1] is essential near the top: it retains the exact codimension $`m` in $`3-\alpha_{g,k}=2m/(2g-1)`. Replacing it by $`k/g` before taking the endpoint limit would change the fixed-codimension denominator.
