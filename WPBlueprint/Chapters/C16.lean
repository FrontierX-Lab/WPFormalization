import WPBlueprint.Chapters.C15
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "appA-kernel-proofs" =>

# Proofs for the kernels and the parameter

This appendix proves Lemmas {bpref "lem:kernel-zeros"}[2.1], {bpref "lem:kernel-positivity"}[2.2] and {bpref "lem:parameter"}[3.1]. Notation is that of Sections 2 and 3.

## Proof of Lemma {bpref "lem:kernel-zeros"}[2.1]

The elementary identities $`X''(y)=-X(y)/y` and $`X'''(y)=\sum_{j\ge0}(-1)^jy^j/(j!(j+2)!)` will also be useful. On $`[0,\pi^2/4]`, $`X(y)>0` for $`y>0`, $`X''<0`, and $`X'''>0`. For the first assertion we use the alternating-series lower bound 

$$`X(y)/y\ge1-y/2+y^2/12-y^3/144>0\quad(0\le y\le5/2);`

 the cubic on the right is decreasing and is positive at $`5/2`. The other assertions follow from the displayed identities and $`X'''(y)\ge1/2-y/6>0`. Similarly, the partial sum of the series for $`a(3/2)` through $`j=4` is an upper bound by the alternating-series test, and it is negative; this proves $`y_0<3/2`. In particular $`X(Y)\le Y<3/2`.

All zeros of $`a(y)` are positive real. Indeed, if $`a(y)=0`, the function $`u(s)=J_0(2\sqrt y\,s)` solves $`(su')'+4ysu=0`, is regular at zero, and vanishes at one. Integration against $`\bar u` gives 

$$`4y\int_0^1s|u|^2\,\mathrm{d}s=\int_0^1s|u'|^2\,\mathrm{d}s>0.`

 The series is entire of order $`1/2`, so its Hadamard product has genus zero and no nonconstant exponential factor. In particular it has no zeros in $`|y|<y_0`.

We next prove that every zero of $`K_Y` is positive and simple. At $`Y=0`, 

$$`K_0(z)=\frac{\sin\sqrt{2z}}{\sqrt{2z}}.`

 Coefficient comparison in {bpref "eq:P1"}[2.1] gives 

$$`\partial_YK_Y=2\partial_zK_Y+(K_Y-a(Y))/z.`

 Integration along the characteristics $`z+2Y=\text{constant}` yields 

$$`\sqrt{t^2-4Y}\ K_Y((t^2-4Y)/2)=\sin t-R_Y(t),\qquad
 R_Y(t)=2\int_0^Y\frac{a(u)}{\sqrt{t^2-4u}}\,\mathrm{d}u.`

 For $`0<Y<y_0` and real $`t>2\sqrt Y`, $`R_Y>0`, $`R_Y'<0`, $`R_Y''>0`, and 

$$`R_Y(t)\le\frac{2X(Y)}{\sqrt{t^2-4Y}}.`

 At $`Y=0`, $`R_0` vanishes identically, as in the sinc formula above. For $`Y>0`, $`\sin t-R_Y(t)` is strictly concave on each positive sine interval. On the first interval $`(2\sqrt Y,\pi)`, it tends to zero at the left endpoint, is positive immediately afterwards by $`K_Y(0)=a(Y)>0`, and is negative at $`\pi`; hence it has exactly one simple interior zero. On $`(2j\pi,(2j+1)\pi)`, $`j\ge1`, it is negative at both endpoints and positive at the midpoint, since 

$$`R_Y((2j+\tfrac12)\pi)
 <\frac3{\sqrt{(5\pi/2)^2-6}}<1.`

 Strict concavity gives exactly two simple zeros there. Negative sine intervals contain no zero. For real $`z\le0`, every argument of $`X'` in {bpref "eq:P1"}[2.1] is less than $`y_0`, where $`X'>0`; for negative arguments this follows from the positive modified-Bessel series. Thus $`K_Y` has no nonpositive real zero.

To exclude nonreal zeros, set $`G_Y(t)=K_Y((t^2-4Y)/2)`. It is entire and even. Formula A.1, with the square root asymptotic to $`t`, holds outside the segment $`[-2\sqrt Y,2\sqrt Y]`. On $`|t|=(N+1/2)\pi`, 

$$`\frac{G_Y(t)}{\sin t/t}
 =\frac t{\sqrt{t^2-4Y}}
    \left(1-\frac{R_Y(t)}{\sin t}\right)=1+O(N^{-1}).`

 The error is uniform: $`R_Y=O(N^{-1})`, and $`|\sin t|` is bounded below on these circles. For the latter assertion use $`|\sin t|\ge\sinh1` when $`|\Im t|\ge1`; otherwise $`|\Re t|` differs from $`(N+1/2)\pi` by $`O(N^{-1})`. Rouché’s theorem gives exactly $`2N` zeros of $`G_Y` inside each sufficiently large circle. The real zeros already counted give exactly $`N` positive and $`N` negative zeros there: for even $`N` the circle ends at the midpoint of a positive sine interval, after its first zero, and for odd $`N` it ends in the subsequent negative interval. They exhaust the count, proving the assertion. Consequently the product formula 2.3 holds. This is again a genus-zero product, since {bpref "eq:P1"}[2.1] has order $`1/2`.

## Proof of Lemma {bpref "lem:kernel-positivity"}[2.2]

We first prove 2.4. By {bpref "eq:P1"}[2.1], 

$$`\partial_YH_Y=2\partial_zH_Y+3(H_Y-a(Y))/z.`

 Writing $`T=\log(a/H_Y)` and $`\gamma=-a'/a`, this becomes 

$$`\partial_YT=-\gamma+2\partial_zT+3(\mathrm{e}^T-1)/z.`

 The constant identity is $`\gamma=5t_1`; for $`m\ge1`, 

$$`t_m'=(2m+5)t_{m+1}
  +3\sum_{\ell=2}^{m+1}\frac1{\ell!}
       \sum_{\substack{i_1+\cdots+i_\ell=m+1\\ i_j\ge1}}
          t_{i_1}\cdots t_{i_\ell}.`

 At $`Y=0`, 

$$`H_0(z)=3\frac{\sin\sqrt{2z}-\sqrt{2z}\cos\sqrt{2z}}
                    {(\sqrt{2z})^3}.`

 Its zeros are positive real. For a direct proof, a nonzero root $`t` of $`\sin t-t\cos t` gives the regular function $`u(s)=j_1(ts)`, satisfying $`(s^2u')'+(t^2s^2-2)u=0` and $`u(1)=0`. Integration against $`\bar u` shows 

$$`t^2\int_0^1s^2|u|^2\,\mathrm{d}s
   =\int_0^1(s^2|u'|^2+2|u|^2)\,\mathrm{d}s>0.`

 Here $`j_1(w)=\sin w/w^2-\cos w/w` is regular at zero. The root is simple because $`(\sin t-t\cos t)'=t\sin t` does not vanish at a nonzero root. The order-$`1/2` product therefore gives $`t_m(0)=m^{-1}\sum_j\rho_j^{-m}>0`.

Induct on the derivative order $`q`, simultaneously for all indices $`m`, in A.3. Every differentiated term is a product of derivatives of order at most $`q` with nonnegative coefficients, so the induction is valid; each fixed equation has only finitely many terms. For each $`m`, $`t_m(Y)` is a polynomial in the ratios $`X^{(j)}(Y)/a(Y)`, so it is analytic on $`|Y|<y_0`, and its Taylor series converges to $`t_m(Y)` there. This proves 2.4, and gives strictly positive coefficients of $`H_Y^{-h}` for every real $`h>0`, and nonnegative coefficients of $`-H_Y'/H_Y`.

The same argument applied to $`S=\log(a/K_Y)=\sum_{m\ge1}s_m(Y)z^m` gives 

$$`s_m'=(2m+3)s_{m+1}
  +\sum_{\ell=2}^{m+1}\frac1{\ell!}
       \sum_{\substack{i_1+\cdots+i_\ell=m+1\\ i_j\ge1}}
           s_{i_1}\cdots s_{i_\ell}.`

 The initial sinc product and the same analytic argument imply that every Taylor coefficient in $`Y` of 

$$`\widehat\vartheta_\ell(Y):=a(Y)[z^\ell]K_Y(z)^{-1}`

 is nonnegative. The product for $`a` implies the same for $`a^{-1}` and for $`\vartheta_\ell=[z^\ell]K_Y^{-1}`. This completes the proof.

## Proof of Lemma {bpref "lem:parameter"}[3.1]

We use from Lemma {bpref "lem:kernel-zeros"}[2.1] that $`X>0`, $`X''<0` and $`X'''>0` on the relevant interval, and that $`0<y_0<3/2`.

Normalize the left side of {bpref "eq:SP1"}[1.2] by $`2\sqrt{T-Y}`. Its root equation becomes 

$$`Q(Y,T)=\int_0^1X'(T(1-s^2)+Ys^2)\,\mathrm{d}s=0.`

 It is strictly decreasing in $`T`. At $`T=y_0` it is positive when $`Y<y_0`. The series and the beta integral give the Sonine identity 

$$`\int_0^T\frac{X'(v)}{\sqrt{T-v}}\,\mathrm{d}v
       =\sin(2\sqrt T).`

 At $`T_0=\pi^2/4`, the full integral is zero, and removing $`[0,Y]` makes it negative when $`Y>0`. This proves existence and uniqueness in {bpref "eq:SP1"}[1.2], including $`T(0)=T_0`. The derivative $`Q_T` never vanishes there, so the implicit function theorem gives analyticity. Also $`T'<0`, and $`T\to y_0` as $`Y\to y_0`.

Twice differentiating A.5, with $`v=T(1-s^2)+Ys^2`, gives 

$$`T''(Y)=
 -\frac{\int_0^1X'''(v)[T'(1-s^2)+s^2]^2\,\mathrm{d}s}
        {\int_0^1X''(v)(1-s^2)\,\mathrm{d}s}>0.`

 At $`(Y,T)=(0,T_0)`, A.6 gives $`Q_T=Q_Y=-1/(2T_0)`, and hence $`T'(0)=-1`. Consequently $`-1\le T'<0`.

The integral $`I` is positive. Indeed, subtracting $`(T-y_0)` times {bpref "eq:SP1"}[1.2] from its definition gives 

$$`I(Y)=\int_Y^T
 \frac{X'(v)(y_0-v)}{\sqrt{T-v}}\,\mathrm{d}v>0.`

 Introduce $`J` and $`\beta` as in 3.1. The equality for $`J` is integration by parts, and the last equality for $`\beta` follows from the definition of $`\lambda`. If $`Q_2=\int_0^1s^2X'(T-\Delta s^2)\,\mathrm{d}s`, then $`Q_2>0`: the function $`X'(T-\Delta s^2)` is strictly increasing in $`s` and has mean zero by A.5. Moreover $`Q_2\le X'(Y)/3`. Differentiating $`J` gives 

$$`J'=(1-T')Q_2\le\frac23X'(Y),
 \qquad
 \beta'=\frac{X'J-XJ'}{J^2}\ge\frac{X'}{3J}>0.`

 At zero, A.6 gives $`I(0)=\pi/4`, $`J(0)=1/2`, and $`\lambda(Y)=4Y+O(Y^2)`. At the other endpoint $`J\to x_c` and $`X(Y)\to x_c`, so $`\beta\to1`. This proves the asserted analytic bijection and the values in {bpref "eq:SP3"}[1.7] at zero.

The endpoint constants are also explicit. Put $`\delta=y_0-Y` and $`b=-X''(y_0)=x_c/y_0>0`. The implicit equation at $`(y_0,y_0)` has $`T'=-1/2`; this gives the first formula in 3.2. For the second formula, substitute $`X'(T-\Delta s^2)=b\Delta(s^2-1/3)+O(\Delta^2)` into $`I=2\Delta^{3/2}\int_0^1s^2X'(T-\Delta s^2)\mathrm{d}s`. Together with $`X(Y)\to x_c`, this proves 3.3, and 3.4 follows from {bpref "eq:SP3"}[1.7]. Since $`1-\beta=2/(2+\lambda)`, 3.3 also gives $`\Delta\asymp\sqrt{1-\beta}`.

By part (ii), $`\Psi` is analytic and strictly increasing for $`0<x<x_c`. The first line of 3.5 follows from $`\lambda(Y)=4Y+O(Y^2)` and $`x=X(Y)=Y+O(Y^2)`. For the second line, quadratic inversion gives $`x_c-x=(b/2)\delta^2(1+O(\delta))`. Combining this with 3.2 and 3.3 gives the constant $`5/4`. All expansions here arise from convergent analytic expansions in $`x` or $`\sqrt\varepsilon`, so their asserted derivatives follow by termwise differentiation. In particular $`\Psi^2/(\mathscr D\Psi)` has finite endpoint limits $`0` and $`5/4`, and is bounded on the full interval.
