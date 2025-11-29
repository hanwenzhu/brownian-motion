import Architect
import BrownianMotion.Auxiliary.Adapted
import BrownianMotion.Auxiliary.Algebra
import BrownianMotion.Auxiliary.Analysis
import BrownianMotion.Auxiliary.ContinuousBilinForm
import BrownianMotion.Auxiliary.ENNReal
import BrownianMotion.Auxiliary.FiniteInf
import BrownianMotion.Auxiliary.HasGaussianLaw
import BrownianMotion.Auxiliary.HasLaw
import BrownianMotion.Auxiliary.IsStoppingTime
import BrownianMotion.Auxiliary.Jensen
import BrownianMotion.Auxiliary.LinearAlgebra
import BrownianMotion.Auxiliary.Martingale
import BrownianMotion.Auxiliary.MeanInequalities
import BrownianMotion.Auxiliary.MeasureTheory
import BrownianMotion.Auxiliary.Metric
import BrownianMotion.Auxiliary.NNReal
import BrownianMotion.Auxiliary.Nat
import BrownianMotion.Auxiliary.Real
import BrownianMotion.Auxiliary.StoppedProcess
import BrownianMotion.Auxiliary.Topology
import BrownianMotion.Auxiliary.WithLp
import BrownianMotion.Auxiliary.WithTop
import BrownianMotion.Continuity.Chaining
import BrownianMotion.Continuity.CoveringNumber
import BrownianMotion.Continuity.HasBoundedInternalCoveringNumber
import BrownianMotion.Continuity.IsKolmogorovProcess
import BrownianMotion.Continuity.KolmogorovChentsov
import BrownianMotion.Continuity.KolmogorovChentsovInequality
import BrownianMotion.Gaussian.BrownianMotion
import BrownianMotion.Gaussian.CovMatrix
import BrownianMotion.Gaussian.Fernique
import BrownianMotion.Gaussian.Gaussian
import BrownianMotion.Gaussian.GaussianProcess
import BrownianMotion.Gaussian.Moment
import BrownianMotion.Gaussian.MultivariateGaussian
import BrownianMotion.Gaussian.ProjectiveLimit
import BrownianMotion.Gaussian.StochasticProcesses
import BrownianMotion.StochasticIntegral.ApproxSeq
import BrownianMotion.StochasticIntegral.Cadlag
import BrownianMotion.StochasticIntegral.Centering
import BrownianMotion.StochasticIntegral.ClassD
import BrownianMotion.StochasticIntegral.DoobLp
import BrownianMotion.StochasticIntegral.DoobMeyer
import BrownianMotion.StochasticIntegral.Komlos
import BrownianMotion.StochasticIntegral.LocalMartingale
import BrownianMotion.StochasticIntegral.LocalMonad
import BrownianMotion.StochasticIntegral.Locally
import BrownianMotion.StochasticIntegral.MathlibImports
import BrownianMotion.StochasticIntegral.OptionalSampling
import BrownianMotion.StochasticIntegral.Predictable
import BrownianMotion.StochasticIntegral.QuadraticVariation
import BrownianMotion.StochasticIntegral.SimpleProcess
import BrownianMotion.StochasticIntegral.UniformIntegrable
import BrownianMotion.Verso.Brownian
import BrownianMotion.Verso.Processes

attribute [blueprint
  "thm:ext_of_charFunDual"
  (statement := /-- In a separable Banach space, if two finite measures have same characteristic
    function, they are equal. -/)]
  MeasureTheory.Measure.ext_of_charFunDual

attribute [blueprint
  "lem:charFunDual_map"
  (statement := /-- Let $\mu$ be a measure on a normed space $E$ and let $L$ be a continuous linear
    map from $E$ to $F$.
    Then for all $L' \in F^*$,
    \begin{align*}
      \widehat{L_*\mu}(L') = \hat{\mu}(L' \circ L) \: .
    \end{align*} -/)
  (latexEnv := "lemma")]
  MeasureTheory.charFunDual_map

attribute [blueprint
  "def:covarianceBilin"
  (title := "Covariance")
  (statement := /-- The covariance bilinear form of a measure $\mu$ on $F$ with finite second moment
    is the continuous bilinear form $C_\mu : F^* \times F^* \to \mathbb{R}$ with
    \begin{align*}
      C_\mu(L_1, L_2)
      &= \int_x (L_1(x) - L_1(m_\mu)) (L_2(x) - L_2(m_\mu)) \: d\mu(x)
      \\
      &= \int_x L_1(x - m_\mu) L_2(x- m_\mu) \: d\mu(x)
      \: .
    \end{align*} -/)]
  ProbabilityTheory.covarianceBilinDual

attribute [blueprint
  "def:covarianceBilin"
  (title := "Covariance")
  (statement := /-- The covariance bilinear form of a measure $\mu$ on $F$ with finite second moment
    is the continuous bilinear form $C_\mu : F^* \times F^* \to \mathbb{R}$ with
    \begin{align*}
      C_\mu(L_1, L_2)
      &= \int_x (L_1(x) - L_1(m_\mu)) (L_2(x) - L_2(m_\mu)) \: d\mu(x)
      \\
      &= \int_x L_1(x - m_\mu) L_2(x- m_\mu) \: d\mu(x)
      \: .
    \end{align*} -/)]
  ProbabilityTheory.covarianceBilinDual_apply

attribute [blueprint
  "def:covarianceBilin"
  (title := "Covariance")
  (statement := /-- The covariance bilinear form of a measure $\mu$ on $F$ with finite second moment
    is the continuous bilinear form $C_\mu : F^* \times F^* \to \mathbb{R}$ with
    \begin{align*}
      C_\mu(L_1, L_2)
      &= \int_x (L_1(x) - L_1(m_\mu)) (L_2(x) - L_2(m_\mu)) \: d\mu(x)
      \\
      &= \int_x L_1(x - m_\mu) L_2(x- m_\mu) \: d\mu(x)
      \: .
    \end{align*} -/)]
  ProbabilityTheory.covarianceBilinDual_apply'

attribute [blueprint
  "lem:map_eq_iff"
  (statement := /-- Let $X, Y : T \to \Omega \to E$ be two stochastic processes.
    Then $X$ and $Y$ have same finite-dimensional distributions if and only if they have the same
    law. -/)
  (proof := /-- TODO: consider the $\pi$-system of cylinder sets. -/)
  (latexEnv := "lemma")]
  ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq

attribute [blueprint
  "lem:isGaussian_conv"
  (statement := /-- The convolution of two Gaussian measures is a Gaussian measure. -/)
  (latexEnv := "lemma")]
  ProbabilityTheory.isGaussian_conv

attribute [blueprint
  "thm:exists_integrable_exp_sq_of_map_rotation_eq_self"
  (statement := /-- Let $\mu$ be a finite measure on $F$ such that $\mu \times \mu$ is invariant
    under the rotation of angle $-\frac{\pi}{4}$.
    Then there exists $C > 0$ such that the function $x \mapsto \exp (C \Vert x \Vert ^ 2)$ is
    integrable with respect to $\mu$. -/)]
  ProbabilityTheory.exists_integrable_exp_sq_of_map_rotation_eq_self

attribute [blueprint
  "lem:IsGaussian.map_rotation_eq_self"
  (statement := /-- For a centered Gaussian measure $\mu$, $\mu \times \mu$ is invariant by
    rotation. -/)
  (latexEnv := "lemma")]
  ProbabilityTheory.IsGaussian.map_rotation_eq_self_of_forall_strongDual_eq_zero

attribute [blueprint
  "thm:IsGaussian.exists_integrable_exp_sq"
  (title := "Fernique's theorem")
  (statement := /-- For a Gaussian measure, there exists $C > 0$ such that the function $x \mapsto
    \exp (C \Vert x \Vert ^ 2)$ is integrable. -/)]
  ProbabilityTheory.IsGaussian.exists_integrable_exp_sq

attribute [blueprint
  "def:gramMatrix"
  (title := "Gram matrix")
  (statement := /-- Let $v_1, \ldots, v_n$ be vectors in an inner product space $E$.
    The Gram matrix of $v_1, \ldots, v_n$ is the matrix in $\mathbb{R}^{n \times n}$ with entries
    $G_{ij} = \langle v_i, v_j \rangle$ for $1 \leq i,j \leq n$. -/)]
  Matrix.gram

attribute [blueprint
  "def:logSizeRadius"
  (statement := /-- Let $V$ be a finite subset of a metric space and let $t \in V$ and $a > 1$, $c >
    0$.
    Let the \emph{log-size radius} of $t$ in $V$, denoted by $r_{V,t}$, be the smallest positive
    integer $r$ such that $\vert B_V(t, r c) \vert \le a^{r}$. -/)]
  PairReduction.logSizeRadius

attribute [blueprint
  "lem:card_logSizeRadius_ge"
  (statement := /-- $a^{r_{V,t}-1} \le \vert B_V(t, (r_{V,t}-1)c) \vert$~. -/)
  (latexEnv := "lemma")]
  PairReduction.pow_logSizeRadius_le_card_le_logSizeRadius

attribute [blueprint
  "lem:card_logSizeRadius_le"
  (statement := /-- $\vert B_V(t, r_{V,t}c) \vert \le a^{r_{V,t}}$~. -/)
  (latexEnv := "lemma")]
  PairReduction.card_le_logSizeRadius_le_pow_logSizeRadius

attribute [blueprint
  "def:logSizeBallSequence"
  (title := "Log-size ball sequence")
  (statement := /-- Let $(T,d_T)$ be a metric space and let $J \subseteq T$ be finite, $a,c \in
    \mathbb R_+$ with $a \ge 1$ and $n \in \{1, 2, ...\}$ such that $|J| \le a^n$.
    An log-size ball sequence for $(J, a, c, n)$ is a sequence of $(V_i, t_i, r_i)_{i \in
    \mathbb{N}}$ such that
    \begin{itemize}
      \item $V_0 = J$, $t_0$ is an arbitrary point in $J$,
      \item for all $i$, $r_i$ is the log-size radius of $t_i$ in $V_i$,
      \item $V_{i+1} = V_i \setminus B_{V_i}(t_i, (r_i - 1)c)$, $t_{i+1}$ is arbitrarily chosen in
      $V_{i+1}$.
    \end{itemize} -/)]
  PairReduction.logSizeBallSeq

attribute [blueprint
  "lem:logSizeRadius_logSizeBallSequence_le"
  (statement := /-- The radius of a log-size ball sequence $(V_i, t_i, r_i)_{i \in \mathbb{N}}$ for
    $(J, a, c, n)$ satisfies $r_i \le n$ for all $i \in \mathbb{N}$. -/)
  (proof := /-- Since $|J| \le a^n$, we have $\vert B_{V_i}(t_i, n c) \vert \le \vert J \vert \le
    a^{n}$. -/)
  (latexEnv := "lemma")]
  PairReduction.radius_logSizeBallSeq_le

attribute [blueprint
  "lem:logSizeBallSequence_V_anti"
  (statement := /-- The sets $V_i$ of a log-size ball sequence $(V_i, t_i, r_i)_{i \in \mathbb{N}}$
    are a decreasing sequence of sets. That is, $V_{i+1} \subseteq V_i$ for all $i \in \mathbb{N}$.
    -/)
  (proof := /-- $V_{i+1} = V_i \setminus B_{V_i}(t_i, (r_i - 1)c)$ hence $V_{i+1} \subseteq V_i$. -/)
  (latexEnv := "lemma")]
  PairReduction.finset_logSizeBallSeq_add_one_subset

attribute [blueprint
  "lem:logSizeBallSequence_eq_zero"
  (statement := /-- For any log-size ball sequence $(V_i, t_i, r_i)_{i \in \mathbb{N}}$ for $(J, a,
    c, n)$, for all $k \ge \vert J \vert$, $V_k = \emptyset$. -/)
  (proof := /-- $V_{i+1} = V_i \setminus B_{V_i}(t_i, (r_i - 1)c)$ and since $t_i \in B_{V_i}(t_i,
    (r_i - 1)c)$, we have $\vert V_{i+1} \vert < \vert V_i \vert$ and the cardinal eventually
    reaches $0$, in at most $\vert J \vert$ steps. -/)
  (latexEnv := "lemma")]
  PairReduction.card_finset_logSizeBallSeq_card_eq_zero

attribute [blueprint
  "lem:logSizeBallSequence_disjoint_B"
  (statement := /-- For $i \ne j$, the balls $B_{V_i}(t, (r_i-1)c)$ and $B_{V_j}(t_j, (r_j-1)c)$ of
    a log-size ball sequence $(V_i, t_i, r_i)_{i \in \mathbb{N}}$ are disjoint. -/)
  (proof := /-- Assume w.l.o.g. that $i < j$.
    Then $B_{V_j}(t_j, (r_j-1)c) \subseteq V_j \subseteq V_{i+1}$.
    It suffices to show that $B_{V_i}(t_i, (r_i-1)c)$ and $V_{i+1}$ are disjoint.
    This follows from the definition of $V_{i+1} = V_i \setminus B_{V_i}(t_i, (r_i-1)c)$. -/)
  (latexEnv := "lemma")]
  PairReduction.disjoint_smallBall_logSizeBallSeq

attribute [blueprint
  "def:pairSet"
  (statement := /-- Let $(V_i, t_i, r_i)_{i \in \mathbb{N}}$ be a log-size ball sequence for $(J, a,
    c, n)$.
    For $i \in \mathbb{N}$, let $K_i = \{t_i\} \times B_{V_i}(t_i, r_i c)$ be the set of pairs
    $(t_i, s)$ for $s$ in the ball $B_{V_i}(t_i, r_i c)$.
    We define $K = \bigcup_{i=0}^{\vert J \vert-1} K_i$, set of all pairs from the log-size ball
    sequence. -/)]
  PairReduction.pairSet

attribute [blueprint
  "lem:card_pairSet_le"
  (statement := /-- The cardinal of the pair set $K$ of a log-size ball sequence for $(J, a, c, n)$
    satisfies $|K| \le a |J|$. -/)
  (proof := /-- Using Lemma~\ref{lem:card_logSizeRadius_le}, the cardinal of $K$ is bounded by
    \begin{align*}
      \vert K \vert
      &\le \sum_{i=0}^{m-1} \vert K_i \vert
      \le \sum_{i=0}^{m-1} a^{r_i}
      \: .
    \end{align*}
    Since the sets $B_{V_i}(t_i, (r_i-1)c)$ are disjoint by
    Lemma~\ref{lem:logSizeBallSequence_disjoint_B}, we can use Lemma~\ref{lem:card_logSizeRadius_ge}
    to get
    \begin{align*}
      \sum_{i=0}^{m-1} a^{r_i - 1}
      \le \sum_{i=0}^{m-1} \vert B_{V_i}(t_i, (r_i-1)c) \vert
      = \left\vert \bigcup_{i=0}^{m-1} B_{V_i}(t_i, (r_i-1)c) \right\vert
      \le \vert J \vert
      \: .
    \end{align*}
    We obtained the inequality $\vert K \vert \le a \vert J \vert$ -/)
  (latexEnv := "lemma")]
  PairReduction.card_pairSet_le

attribute [blueprint
  "lem:dist_le_of_mem_pairSet"
  (statement := /-- Let $(s, t)$ be a pair in the pair set $K$ of a log-size ball sequence for $(J,
    a, c, n)$.
    Then $d_T(s, t) \le c n$. -/)
  (proof := /-- A pair $(t, s) \in K$ is of the form $(t_i, s)$ for $s \in B_V(t_i, r_i c)$ and
    satisfies
    \begin{align*}
      d_T(t_i, s) \le c r_i \le c n \: .
    \end{align*}
    The last inequality is from Lemma~\ref{lem:logSizeRadius_logSizeBallSequence_le}. -/)
  (latexEnv := "lemma")]
  PairReduction.edist_le_of_mem_pairSet

attribute [blueprint
  "lem:sup_dist_le_two_mul_sup_dist_pairSet"
  (statement := /-- Let $K$ be the pair set of a log-size ball sequence $(V_i, t_i, r_i)_{i \in
    \mathbb{N}}$ for $(J, a, c, n)$.
    Then for any function $f : T \to E$ with $(E,d_E)$ a metric space,
    \begin{align*}
      \sup_{s,t\in J, d_T(s,t) \le c} d_E(f(s), f(t))
      & \le 2 \sup_{(s,t) \in K} d_E(f(s), f(t))
      \: .
    \end{align*} -/)
  (proof := /-- Let $(s, t) \in J^2$ such that $d_T(s, t) \le c$.
    Then there exists a largest $\ell \in \mathbb{N}$ such that $s, t \in V_\ell$.
    Assume w.l.o.g. that $s \notin V_{\ell + 1}$. Then $s \in B_{V_\ell}(t_\ell, (r_\ell-1)c)$
    (since $V_{\ell + 1} = V_\ell \setminus B_{V_\ell}(t_\ell, (r_\ell-1)c)$), which implies $d_T(s,
    t_\ell) \le (r_\ell - 1)c$.
    
    Since $d_T(s, t) \le c$, $d_T(t, t_\ell) \le d_T(t, s) + d_T(s, t_\ell) \le r_\ell c$, hence $t
    \in B_{V_\ell}(t_\ell, r_\ell c)$ and we have that both $s$ and $t$ are in $B_{V_\ell}(t_\ell,
    r_\ell c)$.
    Thus both $(t_\ell, s)$ and $(t_\ell, t)$ are in $K_\ell \subseteq K$.
    Finally
    \begin{align*}
      d_E(f(s), f(t))
      &\le d_E(f(s), f(t_\ell)) + d_E(f(t_\ell), f(t))
      \\
      &\le 2\sup_{(s',t') \in K} d_E(f(s'), f(t'))
      \: .
    \end{align*} -/)
  (latexEnv := "lemma")]
  PairReduction.iSup_edist_pairSet

attribute [blueprint
  "lem:IsKolmogorovProcess.aemeasurable"
  (statement := /-- If $X : T \to \Omega \to E$ is a function that satisfies the Kolmogorov
    condition, then for all $t \in T$, $X_t$ is $\mathbb{P}$-a.e. measurable. -/)
  (latexEnv := "lemma")]
  ProbabilityTheory.IsAEKolmogorovProcess.aemeasurable

attribute [blueprint
  "lem:IsKolmogorovProcess.aemeasurable_edist"
  (statement := /-- If $X : T \to \Omega \to E$ is a process that satisfies the Kolmogorov
    condition, then for all $s,t \in T$ the function $\omega \mapsto d_E(X_s(\omega), X_t(\omega))$
    is $\mathbb{P}$-a.e. measurable. -/)
  (latexEnv := "lemma")]
  ProbabilityTheory.IsAEKolmogorovProcess.aemeasurable_edist

attribute [blueprint
  "lem:Submartingale.integrable_stoppedValue"
  (statement := /-- Let $X$ be a submartingale. Then for all bounded stopping times $\tau$, the
    stopped value $X_\tau$ is integrable. -/)
  (latexEnv := "lemma")]
  MeasureTheory.Submartingale.integrable_stoppedValue

attribute [blueprint
  "def:StoppingTimeGen"
  (title := "$\\sigma$-algebra generated by a stopping time")
  (statement := /-- Given a stopping time $\tau$ on a time index $T$, define
    $\mathcal{F}_\tau = \bigcup_{t \in T} \{A \in \mathcal{F} \mid A \cap \{\tau \le t\} \in
    \mathcal{F}_t\}.$ -/)]
  MeasureTheory.IsStoppingTime.measurableSpace

attribute [blueprint
  "lem:StoppingTimeGenMono"
  (statement := /-- Let $\tau, \sigma$ be stopping times such that $\tau \le \sigma$.
    Then, $\mathcal{F}_\tau \subseteq \mathcal{F}_\sigma$. -/)
  (latexEnv := "lemma")]
  MeasureTheory.IsStoppingTime.measurableSpace_mono

attribute [blueprint
  "lem:Submartingale.stoppedProcess"
  (statement := /-- Let $X : \mathbb{N} \to \Omega \to \mathbb{R}$ be a sub-martingale and $\tau$ a
    stopping time with respect to the filtration $\mathcal{F}$.
    Then, the stopped process $X^{\tau}$ is a sub-martingale with respect to the filtration
    $\mathcal{F}$. -/)
  (latexEnv := "lemma")]
  MeasureTheory.Submartingale.stoppedProcess

attribute [blueprint
  "def:hittingAfter"
  (title := "Hitting time")
  (statement := /-- For $X : T \to \Omega \to E$ a stochastic process, $B$ a subset of $E$ and $t_0
    \in T$, the hitting time of $X$ in $B$ after $t_0$ is the random variable $\Omega \to
    T\cup\{\infty\}$ defined by
    \begin{align*}
      \tau_{B, t_0}(\omega) = \inf\{t \in T \mid t \ge t_0, \: X_t(\omega) \in B\} \: ,
    \end{align*}
    in which the infimum is infinite if the set is empty. -/)]
  MeasureTheory.hittingAfter

attribute [blueprint
  "lem:Predictable.progressive"
  (statement := /-- A predictable process is progressively measurable. -/)
  (proof := /-- Let $X : T \times \Omega \to E$ be a predictable process, we will show that it is
    progressively measurable. Namely, fixing $t \in T$, denoting
    $$\iota_t : [0, t] \to T : s \mapsto s$$
    we need to show that $\iota_t \circ X : [0, t] \times \Omega \to E$ is measurable with respect
    to $\mathcal{B}([0, t]) \otimes \mathcal{F}_t$.
    
    Denoting $\Sigma_{\mathcal{F}}$ for the predictable $\sigma$-algebra generated by $\mathcal{F}$,
    as $u$ is predictable, we have that $X^{-1}(\mathcal{B}(E)) \le \Sigma_{\mathcal{F}}$. Thus, to
    show that $\iota_t \circ X$ is $\mathcal{B}([0, t]) \otimes \mathcal{F}_t$-measurable, it
    suffices to show that $\iota_t^{-1}(\Sigma_{\mathcal{F}}) \le \mathcal{B}([0, t]) \otimes
    \mathcal{F}_t$. In particular, as
    $$\Sigma_{\mathcal{F}} = \sigma(\{(s, \infty) \times A \mid A \in \mathcal{F}_s\} \cup
    \{\{\perp\} \times A \mid A \in \mathcal{F}_\perp\})$$
    is suffices to show that sets of the form $\iota_t^{-1}((s, \infty) \times A)$ for some $s \in
    T, A \in \mathcal{F}_s$ and $\iota_t^{-1}(\{\bot\} \times A)$ for some $A \in \mathcal{F}_\bot$
    are $\mathcal{B}([0, t]) \otimes \mathcal{F}_t$-measurable.
    
    Indeed, if $A \in \mathcal{F}_\bot$
    $$\iota_t^{-1}(\{\bot\} \times A) = \{\bot\} \times A$$
    while for any $s \in T$ and $A \in \mathcal{F}_s$,
    $$\iota_t^{-1}((s, \infty) \times A) = \begin{cases}
        \varnothing, & t < s\\
        (s, t] \times A, & s \le t.
    \end{cases}$$
    By the monotonicity of the filtration $\mathcal{F}$, all of these cases are $\mathcal{B}([0, t])
    \otimes \mathcal{F}_t$-measurable allowing us to conclude. -/)
  (latexEnv := "lemma")]
  MeasureTheory.IsPredictable.progMeasurable

attribute [blueprint
  "def:martingalePart"
  (statement := /-- Let $X : \mathbb{N} \to \Omega \to E$ be a process indexed by $\mathbb{N}$, for
    $E$ a Banach space.
    Let $(\mathcal{F}_n)_{n\in\mathbb{N}}$ be a filtration on $\Omega$ and let $A$ be the
    predictable part of $X$ for that filtration.
    The martingale part of $X$ is the process $M : \mathbb{N} \to \Omega \to E$ defined by $M_n =
    X_n - A_n$. -/)]
  MeasureTheory.martingalePart

attribute [blueprint
  "lem:martingale_martingalePart"
  (statement := /-- Suppose that the filtration is sigma-finite.
    Then the martingale part of an adapted process $X$ such that $X_n$ is integrable for all $n$ is
    a martingale. -/)
  (latexEnv := "lemma")]
  MeasureTheory.martingale_martingalePart

attribute [blueprint
  "def:isOrderedAddMonoid"
  (title := "Ordered Monoid")
  (statement := /-- Let $(M, +)$ be a commutative monoid that is also a partial order. It is said to
    be an \emph{ordered monoid} if for all $a, b, c \in M$, we have the following implication:
    $$a \le b \implies a + c \le b + c.$$ -/)]
  IsOrderedAddMonoid

attribute [blueprint
  "def:isOrderedModule"
  (title := "Ordered Module")
  (statement := /-- Let $\alpha, \beta$ be preorders with $0$ elements and such that there is a
    scalar multiplication $(\_ \cdot \_) : \alpha \times \beta \to \beta$. Then $\beta$ is said to
    be an \emph{ordered $\alpha$-module} (or \emph{ordered module} if $\alpha$ is clear from the
    context) if the following hold:
    \begin{itemize}
      \item $\forall a \in \alpha, \forall b_1, b_2 \in \beta, 0 \le a \implies b_1 \le b_2 \implies
      a \cdot b_1 \le a \cdot b_2$;
      \item $\forall a_1, a_2 \in \alpha, \forall b \in \beta, 0 \le b \implies a_1 \le a_2 \implies
      a_1 \cdot b \le a_2 \cdot b$.
    \end{itemize} -/)]
  IsOrderedModule

attribute [blueprint
  "def:orderClosedTopology"
  (title := "Order-closed topology")
  (statement := /-- Let $X$ be a topological space that is also a preorder. The space $X$ is set to
    be \emph{order-closed}, or to have \emph{order-closed topology}, if the set $\{(x, y) \in X
    \times X \mid x \le y\}$ is closed. -/)]
  OrderClosedTopology

attribute [blueprint
  "def:limitProcess"
  (statement := /-- Let $X : T \to \Omega \to E$ be a stochastic process, let $\mathcal{F}$ be a
    filtration on $\Omega$ indexed by $T$ and let $P$ be a measure on $\Omega$.
    If there exists a function $Y : \Omega \to E$ which is measurable with respect to
    $\mathcal{F}_\infty$ such that for $P$-almost surely, $X_t$ converges to $Y$ as $t$ goes to
    infinity, then we say that $Y$ is the limit of $X$.
    We denote it by $X_\infty$. -/)]
  MeasureTheory.Filtration.limitProcess

attribute [blueprint
  "lem:maximal_ineq"
  (title := "Doob's maximal inequality for $\\mathbb{N}$")
  (statement := /-- Let $X : \mathbb{N} \rightarrow \Omega \rightarrow \mathbb{R}$ be a non-negative
    sub-martingale.
    Then for every $n \in \mathbb{N}$ and $\lambda > 0$,
    \begin{align*}
      \mathbb{P}\left(\sup_{i \le n}X_i\geq\lambda \right)
      \le \frac{\mathbb{E}\left[X_n \mathbb{I}_{\sup_{i \le n}X_i \ge \lambda}\right]}{\lambda}
      \le \frac{\mathbb{E}[X_n]}{\lambda}
      \: .
    \end{align*} -/)
  (latexEnv := "lemma")]
  MeasureTheory.maximal_ineq

attribute [blueprint
  "def:leastGE"
  (statement := /-- For a process $X : ι \to Ω \to ℝ$ and a real number $a$, define the random time
    \begin{align*}
      \tau_{X \ge a} = \inf\{t \in ι \mid X_t \ge a\} \: ,
    \end{align*}
    in which the infimum is infinite if the set is empty. -/)]
  MeasureTheory.leastGE
