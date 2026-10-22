import Algorithms.Unverified.Muon.Part003

-- Aggregator for `Algorithms.Unverified.Muon`. Source declarations live under `Muon/`.

/-!
# Counterexample to the literal small-J branch in Appendix B.4

Analytic construction and proof outline. The construction and estimates below
remain to be formalized and checked in Lean; this comment is not a proved
Lean theorem and does not discharge any source-facing proof obligation.
The counterexample concerns the literal directional-J implication, not the
separate Jstar condition. Its admissible-schedule quantifiers are stated below.

Claim and quantifiers
---------------------
There is ONE fixed C-infinity scalar objective f, bounded below, with globally
bounded third derivative, a fixed initial point x_0=0, and fixed positive
parameters Delta=f(0)-inf f, sigma=Delta, and a deterministic unbiased oracle,
such that for all sufficiently small epsilon>0, Algorithm 1 with

  B=1, r=1,
  h=epsilon^2/Delta^2,
  eta=h, beta=1-h,
  T=ceil(Delta^3 epsilon^(-3))

satisfies the printed Appendix B.4 parameter scales and J<=epsilon, but

  (1/T) sum_{t=0}^{T-1} |f'(x_t)| = Omega(epsilon^(4/5)).

In particular its ratio to epsilon tends to infinity. This refutes the literal
small-J implication for these admissible schedules. It does not claim failure
for every possible tuning of the hidden Theta constants. It does not refute
the distinct small-Jstar condition appearing in the main-text footnote.

1. Fixed function
-----------------
For x>=0 put z=1+x and define

  q(x)=z^(-6/5),
  phi(x)=(12/7)(z^(7/5)-1),
  p(x)=q(x)(2+sin(phi(x))),
  F(x)=2-p(x)-integral_0^x p(u) du.

Thus F(0)=0, p(0)=2, p'(0)=0, and F'(x)=-p(x)-p'(x).
The identity p'(0)=0 follows from q'(0)=-6/5 and phi'(0)=12/5.

Extend F smoothly to x<0, keeping f(x)>=0 there and f=F on x>=0.
Such an extension is explicit via a smooth cutoff: F's formula is smooth for
x>-1 and F(x)>0 for negative x sufficiently close to zero, since F'(0)=-2.
Choose 0<d<1 inside that interval and a smooth chi equal to 0 for x<=-d
and 1 for x>=-d/2. Set f=chi F+(1-chi) on x>-d and f=1 on x<=-d.
Every derivative is bounded on this compact transition interval.

Since q<=p<=3q and integral_0^infinity q=5, the number I=integral_0^infinity p
is finite and lies in [5,15]. For x>=0,

  F(x)-(2-I)=integral_x^infinity p(u)du-p(x)
             >=5z^(-1/5)-3z^(-6/5)>0.

Therefore inf_R f=2-I, and Delta=I-2 lies in [3,13]. In particular the
objective, its infimum, Delta, sigma, and initial point are independent of
epsilon. The infimum need not be attained; the source assumes only a finite
infimum for this theorem.

2. Regularity and oracle
------------------------
phi'=(12/5)z^(2/5), phi''=(24/25)z^(-3/5),
phi'''=-(72/125)z^(-8/5).

On x>=0, the leading orders of p',p'',p''' are respectively
O(z^(-4/5)), O(z^(-2/5)), O(1); all other derivative terms decay.
Hence f'''=-p''-p''' is globally bounded after the compact extension.
Also f' and f'' are bounded globally. A finite bound s for |f'''| supplies
Assumption 4.13.

Take f(x;xi)=f(x) for every sample. The oracle is unbiased and its variance
is zero, thus <=sigma^2 for the fixed positive sigma=Delta. A positive variance
UPPER BOUND does not require positive actual noise.

3. Actual discrete trajectory, not an arbitrary prescribed sequence
------------------------------------------------------------------
In one dimension the rank-reduced SVD update for nonzero momentum is
x_{t+1}=x_t-eta sign(M_t). Initialization is M_0=f'(0)=-2.

Let S=Th. We prove x_t=th and M_t<0 through the required horizon.
As long as that trajectory holds up to time t, write e_t=M_t+p(th).
The actual momentum recurrence, with alpha=1-beta=h, gives exactly

  e_t=(1-h)e_{t-1}
      +(1-h)[p(th)-p((t-1)h)]-h p'(th).

Set A=sup_{x>=0}|p'(x)|, B2=sup_{x>=0}|p''(x)|, K=A+B2/2, all finite.
The bracketed local error has absolute value at most K h^2, because

  p(th)-p((t-1)h)=h p'(th)+R_t, |R_t|<=B2 h^2/2.

Since e_0=0 and 0<h<1, geometric summation gives |e_t|<=K h.
Meanwhile p(th)>=(1+S)^(-6/5). Here

  S=Delta/epsilon+O(epsilon^2),
  K h (1+S)^(6/5)=O(epsilon^(4/5)) -> 0.

Consequently K h<(1+S)^(-6/5) for sufficiently small epsilon. Induction
therefore gives M_t=-p(th)+e_t<0 and x_{t+1}=(t+1)h throughout the horizon.
No zero-momentum convention or arbitrary direction choice is used.

4. The source small-J hypothesis really holds
--------------------------------------------
Every scalar update direction is -1, so the source directional curvature is
J_t=f''(th). Since f''' is bounded, its Riemann-sum error yields

  J=(1/T)sum_t f''(th)
    =[f'(S)-f'(0)]/S+O(h).

Now f'(0)=-2 and f'(S)=O(S^(-4/5)), hence

  J=2/S+O(S^(-9/5))+O(h),
  J/epsilon -> 2/Delta <= 2/3.

Thus eventually 0<J<=epsilon. The printed r=1 threshold is
sigma Delta^(-1) epsilon=epsilon. This satisfies that threshold even with
upper-bound constant one, rather than merely an unspecified large constant.
The construction is deterministic, so pathwise and expected J agree.

5. The claimed average-gradient conclusion fails
------------------------------------------------
Direct differentiation gives

  f'(x)=-(12/5)z^(-4/5) cos(phi(x))-(q(x)+q'(x))(2+sin(phi(x))).

The second term has integrable absolute value on [0,infinity), with total
integral at most 3 integral q +3 integral |q'| =18.

Let a(x)=z^(-4/5). Using |cos u|>=cos^2 u,

  integral_0^S a|cos phi|
    >=(1/2) integral_0^S a +(1/2) integral_0^S a cos(2phi).

The oscillatory last integral is uniformly bounded by integration by parts:
a/(2phi')=(5/24)z^(-6/5), whose derivative is absolutely integrable.
For example the bound 5/12 suffices. Thus

  integral_0^S |f'(x)|dx >=6(1+S)^(1/5)-25.

Let H=sup_{x>=0}|f''(x)|<infinity. The function |f'| is H-Lipschitz, so

  (1/T)sum_t |f'(th)|
    >=[6(1+S)^(1/5)-25]/S - H h/2
    =Omega(S^(-4/5))=Omega(epsilon^(4/5)).

Dividing by epsilon makes the lower bound tend to infinity. No constant
depending on this fixed objective or fixed problem parameters can make the
average O(epsilon). The expected nuclear-gradient average is exactly this
quantity in the deterministic scalar specialization. A uniform-time sampled
output has the same expected norm.

6. Parameter check
------------------
With sigma=Delta and r=1,

  1-beta=h=epsilon^2/sigma^2,
  eta=h=Delta epsilon^2/sigma^3,
  T=ceil(sigma^3 epsilon^(-3)).

These are precisely admissible choices in the printed schedules, with fixed
constants independent of epsilon. Beta is in [0,1) for small epsilon. B=1.
The true initial gap is Delta, not an independent arbitrary substitute.

Interpretation and limits
-------------------------
The signed Hessian average telescopes to a boundary gradient difference along
the actual monotone trajectory. It is small even though the gradient keeps
oscillating, and its absolute average decays more slowly. The oscillation
frequency increases while amplitudes decay, keeping the third derivative
bounded. This avoids the fixed-positive-step resonance obstruction.

This is a new analytic derivation, not an existing pipeline certificate or
Lean proof. It establishes a counterexample to the literal Appendix B.4
small-J implication with the admissible schedules above. It does not by itself
validate all existing Lean definitions, certify all other Muon conclusions,
or establish that every possible retuning of the schedules must fail.

-/
