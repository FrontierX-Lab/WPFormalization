import WPFormalization.Statements
import WPBlueprint.Chapters.C01
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "02-kernels-parameter" =>

# Positive kernels

Two entire functions of a variable $`z`, depending on the parameter $`Y`, control everything that follows. The first, $`K_Y`, arises in Section 4 when the marking singled out by the Dijkgraaf–Verlinde–Verlinde equation is merged with the $`\kappa_1` insertions: these mergers act on the amplitudes as $`K_Y(E)`, where $`E` raises a degree by one, so the Taylor coefficients of $`1/K_Y` become the coefficients of the recursion. The second, $`H_Y`, plays the same role for the dilaton equation and for the explicit comparison model. The later arguments need three properties: all zeros of $`K_Y` are positive and simple (Lemma {bpref "lem:kernel-zeros"}[2.1]); $`1/K_Y` and $`1/H_Y` have nonnegative Taylor coefficients, even as functions of $`Y` (Lemma {bpref "lem:kernel-positivity"}[2.2]); and after rescaling by the first zero of $`K_Y` both kernels form a compact family, including the endpoint $`Y=y_0` (Subsection 2.2). The last property is what makes all later constants uniform in $`Y`. The first two are special-function statements; their proofs are given in Appendix A.

Recall from Subsection 1.1 that 

$$`X(y)=\sum_{j\ge0}\frac{(-1)^j y^{j+1}}{j!(j+1)!}
      =\sqrt yJ_1(2\sqrt y),\qquad
 a(y)=X'(y)=J_0(2\sqrt y),`

 that $`y_0=j_{0,1}^2/4` is the first positive zero of $`a`, and that $`x_c=X(y_0)`. Thus $`a>0` on $`[0,y_0)`, and the inverse branch $`Y(x)`, with $`Y(0)=0`, maps $`[0,x_c)` onto $`[0,y_0)`.

We shall use

:::definition "eq:P1" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "def:bessel")
%%%
source := { document := "paper-v3", spans := #[{ page := "16", anchor := "eq:P1", citation := "Equation 2.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 2.1 — Positive-recursion kernels.

In the setup and notation of this section, the paper defines or asserts:



$$`\begin{aligned}
 K_Y(z)&=\int_0^1X'\bigl(Y+\tfrac z2(1-s^2)\bigr)\,\mathrm{d}s
       =\sum_{\ell\ge0}\frac{X^{(\ell+1)}(Y)}{(2\ell+1)!!}z^\ell,\\
 H_Y(z)&=3\int_0^1s^2X'\bigl(Y+\tfrac z2(1-s^2)\bigr)\,\mathrm{d}s
       =\sum_{\ell\ge0}\frac{3X^{(\ell+1)}(Y)}{(2\ell+3)!!}z^\ell.
 \end{aligned}`


:::



Beta integration gives the series and hence

:::proposition "eq:P2" (parent := "paper_core") (tags := "paper-new") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "16", anchor := "eq:P2", citation := "Equation 2.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 2.2 — Kernel differential identity.

In the setup and notation of this section, the paper defines or asserts:



$$`K_Y=H_Y+\tfrac23z\partial_zH_Y.`


:::



We write $`r(Y)` for the first positive zero of $`K_Y`; it equals $`2\Delta(Y)`.

## Real zeros and coefficient positivity

:::lemma_ "lem:kernel-zeros" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:P1")
%%%
source := { document := "paper-v3", spans := #[{ page := "16", anchor := "lem:kernel-zeros", citation := "Lemma 2.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma 2.1 — Real zeros.

On $`[0,\pi^2/4]`, $`X(y)>0` for $`y>0`, $`X''<0`, and $`X'''>0`. Moreover $`y_0<3/2`; in particular $`X(Y)\le Y<3/2` for $`0\le Y\le y_0`. All zeros of $`a(y)` are positive real; in particular $`a` has no zeros in $`|y|<y_0`. For $`0\le Y<y_0`, every zero of $`K_Y` is positive and simple, and 

$$`K_Y(z)=a(Y)\prod_{j\ge1}(1-z/r_j(Y)),
 \qquad 0<r_1(Y)<r_2(Y)<\cdots.`


:::



At $`Y=0` one has $`K_0(z)=\sin\sqrt{2z}/\sqrt{2z}`, and the lemma is the classical description of the zeros of the sine function. For $`Y>0`, integration along the characteristics of a first-order equation for $`K_Y` writes $`K_Y` as $`\sin t` minus a small positive correction; concavity then locates the real zeros, and Rouché’s theorem shows that there are no others.

Reality of the zeros of $`K_Y` does not imply it for $`H_Y`; indeed some higher zeros of $`H_Y` can be nonreal. The required substitute is the following stronger coefficient assertion.

:::lemma_ "lem:kernel-positivity" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:P1")
%%%
source := { document := "paper-v3", spans := #[{ page := "17", anchor := "lem:kernel-positivity", citation := "Lemma 2.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma 2.2 — Coefficient positivity.

For $`0\le Y<y_0`, 

$$`\log\frac{a(Y)}{H_Y(z)}=\sum_{m\ge1}t_m(Y)z^m,
 \qquad t_m^{(q)}(0)\ge0\quad(m\ge1,q\ge0),\quad t_m(0)>0,`

 where each $`t_m` is analytic on $`|Y|<y_0` and its Taylor series at zero converges to $`t_m(Y)` there. Consequently $`H_Y^{-h}` has strictly positive Taylor coefficients for every real $`h>0`, and $`-H_Y'/H_Y` has nonnegative coefficients. Moreover every Taylor coefficient in $`Y` of 

$$`\widehat\vartheta_\ell(Y):=a(Y)[z^\ell]K_Y(z)^{-1}`

 is nonnegative, and the same holds for $`a^{-1}` and for $`\vartheta_\ell=[z^\ell]K_Y^{-1}`.
:::



The coefficients $`t_m` satisfy a system of ordinary differential equations in $`Y` whose right-hand sides are polynomials with nonnegative coefficients, and they are positive at $`Y=0`, where $`H_0` has only positive real zeros; induction on the order of differentiation gives the lemma. Note that these are statements about Taylor coefficients in the parameter $`Y`, which is stronger than positivity at each real $`Y`; they supply the positive convolution factor of Section 9.1.

## Rescaled kernels and a local limit theorem

Set $`r=r_1(Y)`,

:::definition "eq:P9" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:P1")
%%%
source := { document := "paper-v3", spans := #[{ page := "17", anchor := "eq:P9", citation := "Equation 2.5", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 2.5 — Compact normalized kernels.

In the setup and notation of this section, the paper defines or asserts:



$$`\bar K_Y(w)=K_Y(rw)/a(Y),\qquad
 \bar H_Y(w)=H_Y(rw)/a(Y),\qquad
 A(Y)=\bar H_Y(1)/3.`


:::



The first zero $`r` is simple and varies analytically. Integration of {bpref "eq:P2"}[2.2] gives 

$$`H_Y(z)=\frac3{2z^{3/2}}\int_0^zv^{1/2}K_Y(v)\,\mathrm{d}v,`

 so $`H_Y(z)>0` on $`[0,r]`. Since $`H_Y^{-1}` has nonnegative Taylor coefficients, its radius of convergence exceeds $`r`. Indeed, by Pringsheim’s theorem a power series with nonnegative coefficients is singular at the positive point of its circle of convergence; if the radius were at most $`r`, that point would be a zero of $`H_Y` in $`(0,r]`. In particular $`H_Y` has no complex zero of modulus at most $`r`.

At the critical endpoint put $`b=-X''(y_0)>0`. The equation $`K_Y(r)=0` and Taylor expansion at $`Y=y_0,r=0` give

:::proposition "eq:P10" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:P9")
%%%
source := { document := "paper-v3", spans := #[{ page := "17", anchor := "eq:P10", citation := "Equation 2.6", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 2.6 — Critical kernel limits.

In the setup and notation of this section, the paper defines or asserts:



$$`r(Y)\sim3a(Y)/b,\qquad
 \bar K_Y(w)\longrightarrow1-w,\qquad
 \bar H_Y(w)\longrightarrow1-3w/5.`


:::



These convergences are locally uniform in complex $`w`. The family therefore extends continuously to $`Y=y_0`. Compactness and nonvanishing on the closed unit disk give one $`\eta>0` such that all $`\bar H_Y^{-1}` are analytic and uniformly bounded on $`|w|\le1+\eta`, including this endpoint. Likewise $`\bar K_Y/(1-w)` is nonvanishing on a common disk of radius greater than one: its zeros are the higher positive roots from 2.3, and {bpref "eq:P10"}[2.6] treats the endpoint. Consequently, with $`\theta_{-1}=0`,

:::proposition "eq:P11" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:P9")
%%%
source := { document := "paper-v3", spans := #[{ page := "17", anchor := "eq:P11", citation := "Equation 2.7", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 2.7 — Uniform kernel moments.

In the setup and notation of this section, the paper defines or asserts:



$$`1=\theta_0\le\theta_1\le\cdots\le C,
 \quad \theta_\ell=[w^\ell]\bar K_Y(w)^{-1},
 \quad w_\ell:=\theta_\ell-\theta_{\ell-1}\ge0,
 \quad\sup_Y\sum_{\ell\ge0}(1+\ell)^q w_\ell<\infty.`


:::



Indeed $`\sum w_\ell w^\ell=(1-w)/\bar K_Y(w)` is the inverse product over the higher roots. It has nonnegative coefficients and a common analytic disk. Also $`A(Y)` is bounded above and away from zero.

Finally,

:::definition "eq:P12" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:P9")
%%%
source := { document := "paper-v3", spans := #[{ page := "17", anchor := "eq:P12", citation := "Equation 2.8", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 2.8 — Harmonic probability law.

In the setup and notation of this section, the paper defines or asserts:



$$`P_Y(w)=\frac{\bar H_Y(1)}{\bar H_Y(w)}`


:::



is the probability generating function of a nonnegative integer variable. Its probabilities at zero and one have uniform positive lower bounds, its exponential moments are uniformly bounded, and {bpref "eq:P2"}[2.2] at the first root gives mean $`3/2`. Its variance $`\sigma_Y^2` is bounded above and away from zero. At $`Y=y_0` the law is geometric, with generating function $`(2/5)/(1-3w/5)`, so its variance is $`15/4`.

For a sum $`S_h` of $`h` independent copies, Fourier inversion now gives, uniformly in $`Y` and in integers $`m` with $`|m-3h/2|\le L\sqrt h`, for each fixed $`L`,

:::proposition "eq:P13" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:P12")
%%%
source := { document := "paper-v3", spans := #[{ page := "18", anchor := "eq:P13", citation := "Equation 2.9", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 2.9 — Uniform harmonic local limit.

In the setup and notation of this section, the paper defines or asserts:



$$`\Pr(S_h=m)=\frac1{\sqrt{2\pi h\sigma_Y^2}}
     \exp\!\left(-\frac{(m-3h/2)^2}{2h\sigma_Y^2}\right)
       +o(h^{-1/2}).`


:::



Indeed, on a fixed neighborhood of zero the centered characteristic logarithm is $`-\sigma_Y^2t^2/2+O(|t|^3)`, uniformly by the exponential moments. Away from zero its modulus is uniformly less than one, because the first two probabilities have uniform positive lower bounds. Scaling $`t` by $`h^{-1/2}`, these facts give an integrable Gaussian bound and pointwise convergence; Fourier inversion proves {bpref "eq:P13"}[2.9]. At a bounded displacement from the mean the error is relative $`O(h^{-1})`, by expansion through fourth order and cancellation of the odd cubic integral. Thus 

$$`[w^m]\bar H_Y(w)^{-h}
   =\bar H_Y(1)^{-h}\Pr(S_h=m)`

 has a uniform central lower bound $`c_L\bar H_Y(1)^{-h}/\sqrt h`, and its logarithm at a bounded displacement is $`-h\log\bar H_Y(1)-\tfrac12\log h+O(1)`. These are the coefficient estimates used below.

# The density parameter

This section establishes the properties of the functions $`T`, $`\Delta=T-Y`, $`I` and $`\lambda` defined in {bpref "eq:SP1"}[1.2] and {bpref "eq:SP2"}[1.3]. Their meaning is as follows. The first positive zero of $`K_Y` is $`r(Y)=2\Delta(Y)`; equation {bpref "eq:SP1"}[1.2] is the condition $`K_Y(2\Delta)=0` written in the variable $`v=T-\Delta s^2`. The integral $`I(Y)` is the action that governs the exponential growth in 1.4, and $`\lambda(Y)/2` is the logarithmic derivative of $`I(Y)^{-1}` with respect to $`\log x`, that is, the leading cusp-count scale per unit complexity. Lemma {bpref "lem:parameter"}[3.1] below shows that $`T` is well defined and that $`\lambda` is an analytic increasing bijection from $`[0,y_0)` onto $`[0,\infty)`, so that the profiles $`\mathcal B,\mathcal C` of {bpref "eq:SP3"}[1.7] are functions of the density $`\lambda\ge0`; it also records the behavior of all four functions at the two ends of the interval. Its proof, which uses the Sonine integral and elementary calculus, is given in Appendix A.3.

For the local-limit arguments we view $`\lambda` as a function of the cusp weight and put 

$$`\Psi(x)=\lambda(Y(x))/2,\qquad x=X(Y),\qquad
 \mathscr D=x\frac{\mathrm{d}}{\mathrm{d}x}.`



:::lemma_ "lem:parameter" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP1, eq:SP2")
%%%
source := { document := "paper-v3", spans := #[{ page := "18", anchor := "lem:parameter", citation := "Lemma 3.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma 3.1 — The parameter.

1. The root $`T(Y)` of {bpref "eq:SP1"}[1.2] exists, is unique and depends analytically on $`Y\in[0,y_0)`. One has $`T(0)=\pi^2/4`, $`-1\le T'<0`, $`T''>0`, and $`T\to y_0` as $`Y\to y_0`. Moreover $`I>0`.

2. Put 
   $$`J(Y)=\int_0^1X(T-\Delta s^2)\,\mathrm{d}s
     =X(Y)+\frac{I(Y)}{\sqrt\Delta},
 \qquad
 \beta(Y)=\frac{X(Y)}{J(Y)}=
           \frac{\lambda(Y)}{2+\lambda(Y)}.`
    Then $`\beta'>0`, and $`\lambda` is an analytic strictly increasing bijection from $`[0,y_0)` onto $`[0,\infty)`. At $`Y=0`, $`\Delta=T=\pi^2/4`, $`I(0)=\pi/4`, $`J(0)=1/2`, and $`\lambda(Y)=4Y+O(Y^2)`.

3. Put $`\delta=y_0-Y` and $`b=-X''(y_0)=x_c/y_0>0`. As $`\delta\to0`, 
   $$`\Delta=\frac32\delta+O(\delta^2),\qquad
 I(Y)=\frac{8b}{45}\Delta^{5/2}(1+O(\Delta)),`
    
   $$`\lambda\sim\frac{45x_c}{4b}\Delta^{-2}
       =\frac{45j_{0,1}^2}{16}\Delta^{-2},`
    and consequently 
   $$`\mathcal B(\lambda)\sim
 \frac{\pi^2}{3\sqrt5\,j_{0,1}}\sqrt\lambda,\qquad
 \mathcal C(\lambda)\sim\frac{\pi^2}{x_c}\lambda.`
    Also $`\Delta\asymp\sqrt{1-\beta}`.

4. The function $`\Psi` is analytic and strictly increasing for $`0<x<x_c`. With $`\varepsilon=1-x/x_c`, 
   $$`\begin{array}{ll}
 x\downarrow0:&
 \Psi=2x+O(x^2),\quad\mathscr D\Psi=2x+O(x^2),\quad
 \mathscr D^2\Psi=2x+O(x^2),\\[1mm]
 x\uparrow x_c:&
 \displaystyle\Psi=\frac5{4\varepsilon}(1+O(\sqrt\varepsilon)),\quad
 \mathscr D\Psi=\frac5{4\varepsilon^2}(1+O(\sqrt\varepsilon)),\quad
 \mathscr D^2\Psi=O(\varepsilon^{-3}).
 \end{array}`
    These expansions arise from convergent analytic expansions in $`x` or $`\sqrt\varepsilon`. In particular $`\Psi^2/(\mathscr D\Psi)` has finite endpoint limits $`0` and $`5/4`, and is bounded on the full interval.
:::



The estimate $`\Delta\asymp\sqrt{1-\beta}` in (iii) implies the integrability at one of the logarithmic chain profile in Section 12.
