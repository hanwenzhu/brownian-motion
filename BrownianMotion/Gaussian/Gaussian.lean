import Architect
import BrownianMotion.Gaussian.CovMatrix
import BrownianMotion.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilinDual

/-!
# Facts about Gaussian characteristic function
-/

open Complex MeasureTheory WithLp NormedSpace

open scoped Matrix NNReal Real InnerProductSpace ProbabilityTheory

namespace ProbabilityTheory

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

lemma isGaussian_iff_gaussian_charFunDual [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∃ (m : E) (f : ContinuousBilinForm ℝ (StrongDual ℝ E)),
      f.IsPosSemidef ∧ ∀ L, charFunDual μ L = exp (L m * I - f L L / 2) := by
  refine ⟨fun h ↦ ⟨μ[id], covarianceBilinDual μ, isPosSemidef_covarianceBilinDual, fun L ↦ ?_⟩,
    fun ⟨m, f, hf, h⟩ ↦ ⟨fun L ↦ ?_⟩⟩
  · rw [h.charFunDual_eq, covarianceBilinDual_self_eq_variance]
    · congr
      rw [← L.integral_comp_id_comm', integral_complex_ofReal]
      exact IsGaussian.integrable_id
    exact IsGaussian.memLp_two_id
  have : μ.map L = gaussianReal (L m) (f L L).toNNReal := by
    apply Measure.ext_of_charFun
    ext t
    simp_rw [charFun_map_eq_charFunDual_smul, h, charFun_gaussianReal,
      ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    congr
    · norm_cast
    rw [Real.coe_toNNReal]
    · norm_cast
      ring
    exact hf.nonneg_apply_self L
  rw [eq_gaussianReal_integral_variance this, integral_map (by fun_prop) (by fun_prop),
    variance_map aemeasurable_id (by fun_prop)]
  simp

attribute [simp] ContinuousLinearMap.coe_zero'

lemma gaussian_charFunDual_congr [IsFiniteMeasure μ] {m : E}
    {f : ContinuousBilinForm ℝ (StrongDual ℝ E)}
    (hf : f.IsPosSemidef) (h : ∀ L, charFunDual μ L = exp (L m * I - f L L / 2)) :
    m = ∫ x, x ∂μ ∧ f = covarianceBilinDual μ := by
  have h' := isGaussian_iff_gaussian_charFunDual.2 ⟨m, f, hf, h⟩
  simp_rw [h'.charFunDual_eq, Complex.exp_eq_exp_iff_exists_int, integral_complex_ofReal,
    ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id] at h
  choose n hn using h
  have h L : (n L : ℂ) = (L (∫ x, x ∂μ) * I - Var[L; μ] / 2 - L m * I + f L L / 2) /
      (2 * π * I) := by
    rw [hn L]
    have : 2 * π * I ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
    ring
  have : Continuous n := by
    rw [← Complex.isometry_intCast.comp_continuous_iff]
    change Continuous (fun L ↦ (n L : ℂ))
    simp_rw [h, ← covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id]
    fun_prop
  rw [← IsLocallyConstant.iff_continuous] at this
  apply IsLocallyConstant.eq_const at this
  have this L : n L = 0 := by
    rw [this 0, ← Int.cast_inj (α := ℂ)]
    simp [h]
  simp only [this, Int.cast_zero, zero_mul, add_zero, Complex.ext_iff, sub_re, mul_re, ofReal_re,
    I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, div_ofNat_re, zero_sub, neg_inj, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj', sub_im, mul_im, div_ofNat_im, zero_div,
    sub_zero] at hn
  constructor
  · rw [eq_iff_forall_dual_eq ℝ]
    simp [hn]
  · apply ContinuousBilinForm.ext_of_isSymm hf.isSymm isPosSemidef_covarianceBilinDual.isSymm
    intro x
    rw [covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id]
    exact (hn x).1.symm

/-- Two Gaussian measures are equal if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_covarianceBilinDual {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covarianceBilinDual μ = covarianceBilinDual ν) : μ = ν := by
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [IsGaussian.charFunDual_eq, integral_complex_ofReal,
    L.integral_comp_id_comm' IsGaussian.integrable_id, hm,
    ← covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id, hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_iff_covarianceBilinDual {ν : Measure E} [IsGaussian μ]
    [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covarianceBilinDual μ = covarianceBilinDual ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext_covarianceBilinDual h.1 h.2

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

attribute [blueprint
  "def:charFunDual"
  (title := "Characteristic function")
  (statement := /-- The characteristic function of a measure $\mu$ on a normed space $E$ is the
    function $E^* \to \mathbb{C}$ defined by
    \begin{align*}
      \hat{\mu}(L) = \int_E e^{i L(x)} \: d\mu(x) \: .
    \end{align*} -/)]
  MeasureTheory.charFunDual

attribute [blueprint
  "def:charFun"
  (title := "Characteristic function")
  (statement := /-- The characteristic function of a measure $\mu$ on an inner product space $E$ is
    the function $E \to \mathbb{C}$ defined by
    \begin{align*}
      \hat{\mu}(t) = \int_E e^{i \langle t, x \rangle} \: d\mu(x) \: .
    \end{align*}
    This is equal to the normed space version of the characteristic function applied to the linear
    map $x \mapsto \langle t, x \rangle$. -/)]
  MeasureTheory.charFun

attribute [blueprint
  "thm:isGaussian_iff_charFunDual_eq"
  (statement := /-- A finite measure $\mu$ on $F$ is Gaussian if and only if for every continuous
    linear form $L \in F^*$, the characteristic function of $\mu$ at $L$ is
    \begin{align*}
      \hat{\mu}(L) = \exp\left(i \mu[L] - \mathbb{V}_\mu[L] / 2\right) \: ,
    \end{align*}
    in which $\mathbb{V}_\mu[L]$ is the variance of $L$ with respect to $\mu$. -/)]
  ProbabilityTheory.isGaussian_iff_charFunDual_eq

@[blueprint
  "lem:isGaussian_iff_charFun_eq"
  (statement := /-- A finite measure $\mu$ on a Hilbert space $E$ is Gaussian if and only if for
    every $t \in E$, the characteristic function of $\mu$ at $t$ is
    \begin{align*}
      \hat{\mu}(t) =  \exp\left(i \mu[\langle t, \cdot \rangle] - \mathbb{V}_\mu[\langle t, \cdot
      \rangle] / 2\right) \: .
    \end{align*} -/)
  (proof := /-- By Theorem~\ref{thm:isGaussian_iff_charFunDual_eq}, $\mu$ is Gaussian iff for every
    continuous linear form $L \in E^*$, the characteristic function of $\mu$ at $L$ is
    \begin{align*}
      \hat{\mu}(L) = \exp\left(i \mu[L] - \mathbb{V}_\mu[L] / 2\right) \: .
    \end{align*}
    Every continuous linear form $L \in E^*$ can be written as $L(x) = \langle t, x \rangle$ for
    some $t \in E$, hence we have that $\mu$ is Gaussian iff for every $t \in E$,
    \begin{align*}
      \hat{\mu}(t) = \exp\left(i \mu[\langle t, \cdot \rangle] - \mathbb{V}_\mu[\langle t, \cdot
      \rangle] / 2\right) \: .
    \end{align*} -/)
  (latexEnv := "lemma")]
lemma isGaussian_iff_charFun_eq [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∀ t, charFun μ t = exp (μ[fun x ↦ ⟪t, x⟫_ℝ] * I - Var[fun x ↦ ⟪t, x⟫_ℝ; μ] / 2) := by
  rw [isGaussian_iff_charFunDual_eq]
  constructor
  · intro h t
    convert h (InnerProductSpace.toDualMap ℝ E t)
    exact charFun_eq_charFunDual_toDualMap t
  · intro h L
    simpa using h ((InnerProductSpace.toDual ℝ E).symm L)

variable [SecondCountableTopology E]

attribute [blueprint
  "lem:IsGaussian.memLp_id"
  (statement := /-- A Gaussian measure $\mu$ has finite moments of all orders.
    In particular, there is a well defined mean $m_\mu := \mu[\mathrm{id}]$, and for all $L \in
    F^*$, $\mu[L] = L(m_\mu)$. -/)
  (latexEnv := "lemma")]
  ProbabilityTheory.IsGaussian.memLp_id

@[blueprint
  "lem:IsGaussian.charFun_eq"
  (statement := /-- The characteristic function of a Gaussian measure $\mu$ on $E$ is given by
    \begin{align*}
      \hat{\mu}(t) = \exp\left(i \langle t, m_\mu \rangle - \frac{1}{2} C'_\mu(t, t)\right) \: .
    \end{align*} -/)
  (proof := /-- By Lemma~\ref{lem:isGaussian_iff_charFun_eq}, for every $t \in E$,
    \begin{align*}
      \hat{\mu}(t) = \exp\left(i \mu[\langle t, \cdot \rangle] - \mathbb{V}_\mu[\langle t, \cdot
      \rangle] / 2\right) \: .
    \end{align*}
    By Lemma~\ref{lem:IsGaussian.memLp_id}, $\mu$ has finite first moment and $\mu[\langle t, \cdot
    \rangle] = \langle t, m_\mu \rangle$. By the same lemma, $\mu$ has finite second moment and for
    any $t$ we have $\mathbb{V}_\mu[\langle t, \cdot\rangle] = C'_\mu(t, t)$. -/)
  (latexEnv := "lemma")]
lemma IsGaussian.charFun_eq [IsGaussian μ] (t : E) :
    charFun μ t = exp (⟪t, μ[id]⟫_ℝ * I - covInnerBilin μ t t / 2) := by
  rw [isGaussian_iff_charFun_eq.1 inferInstance]
  congr
  · simp_rw [integral_complex_ofReal, ← integral_inner IsGaussian.integrable_id, id]
  · rw [covInnerBilin_self IsGaussian.memLp_two_id]

attribute [blueprint
  "thm:ext_of_charFun"
  (statement := /-- In a separable Hilbert space, if two finite measures have same characteristic
    function, they are equal. -/)]
  MeasureTheory.Measure.ext_of_charFun

attribute [blueprint
  "lem:charFun_map_eq_charFunDual_smul"
  (statement := /-- Let $\mu$ be a measure on $F$ and let $L \in F^*$. Then
    \begin{align*}
      \widehat{L_*\mu}(x) &= \hat{\mu}(x \cdot L) \: .
    \end{align*} -/)
  (latexEnv := "lemma")]
  MeasureTheory.charFun_map_eq_charFunDual_smul

@[blueprint
  "lem:isGaussian_iff_gaussian_charFun"
  (statement := /-- A finite measure $\mu$ on $E$ is Gaussian if and only if there exists $m \in E$
    and $C$ positive semidefinite such that for all $t \in E$, the characteristic function of $\mu$
    at $t$ is
    \begin{align*}
      \hat{\mu}(t) = \exp\left(i \langle t, m \rangle - \frac{1}{2} C(t, t)\right) \: ,
    \end{align*}
    If that's the case, then $m = m_\mu$ and $C = C'_\mu$. -/)
  (proof := /-- Lemma~\ref{lem:IsGaussian.charFun_eq} states that the characteristic function of a
    Gaussian measure has the wanted form.
    
    Suppose now that there exists $m \in E$ and $C$ positive semidefinite such that for all $t \in
    E$, $\hat{\mu}(t) = \exp\left(i \langle t, m \rangle - \frac{1}{2} C(t, t)\right)$.
    
    We need to show that for all $L \in E^*$, $L_*\mu$ is a Gaussian measure on $\mathbb{R}$.
    Such an $L$ can be written as $\langle u, \cdot \rangle$ for some $u \in E$.
    Let then $u \in E$. We compute the characteristic function of $\langle u, \cdot\rangle_*\mu$ at
    $x \in \mathbb{R}$ with Lemma~\ref{lem:charFun_map_eq_charFunDual_smul}:
    \begin{align*}
      \widehat{\langle u, \cdot\rangle_*\mu}(x)
      &= \hat{\mu}(x \cdot u)
      \\
      &= \exp\left(i x \langle u, m \rangle - \frac{1}{2} x^2 C(u, u)\right)
      \: .
    \end{align*}
    This is the characteristic function of a Gaussian measure on $\mathbb{R}$ with mean $\langle u,
    m \rangle$ and variance $C(u, u)$.
    By Theorem~\ref{thm:ext_of_charFun}, $\langle u, \cdot\rangle_*\mu$ is Gaussian, hence $\mu$ is
    Gaussian.
    
    By Lemma~\ref{lem:IsGaussian.charFun_eq}, we deduce that for any $t \in E$ we have
    $$\exp\left(i\langle t, m \rangle - \frac{1}{2} C(t, t)\right) = \exp\left(i\langle t, m_\mu
    \rangle - \frac{1}{2} C'_\mu(t, t)\right).$$
    In particular, for any $t$ there exists $n_t \in \mathbb{Z}$ such that
    $$i\langle t, m \rangle - \frac{1}{2} C(t, t) = i\langle t, m_\mu \rangle - \frac{1}{2}
    C'_\mu(t, t) + 2i\pi n_t.$$
    We deduce that $n$ is a continuous map from $E$ to $\mathbb{Z}$, and thus must be constant
    because $E$ is connected. By looking at the value at $t = 0$, we deduce that for any $t$, $n_t =
    0$. Looking at real and imaginary parts we obtain that for any $t$,
    $$\langle t, m \rangle = \langle t, m_\mu \rangle \quad \text{and} \quad C(t, t) = C'_\mu(t,
    t).$$
    We immediately deduce that $m = m_\mu$. Moreover, because $C$ and $C'_\mu$ are symmetric, they
    are characterized by their values on the diagonal. Indeed, for any $x, y$,
    $$C(x, y) = \frac{1}{2} (C(x + y, x + y) - C(x, x) - C(y, y)).$$
    We deduce that $C = C'_\mu$. -/)
  (latexEnv := "lemma")]
lemma isGaussian_iff_gaussian_charFun [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∃ (m : E) (f : ContinuousBilinForm ℝ E),
      f.IsPosSemidef ∧ ∀ t, charFun μ t = exp (⟪t, m⟫_ℝ * I - f t t / 2) := by
  rw [isGaussian_iff_gaussian_charFunDual]
  refine ⟨fun ⟨m, f, hf, h⟩ ↦ ⟨m,
    f.bilinearComp (InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap
      (InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap,
    ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩, ?_⟩,
    fun ⟨m, f, hf, h⟩ ↦ ⟨m,
      f.bilinearComp (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
        (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap,
    ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩, ?_⟩⟩
  · simp [hf.isSymm.map_symm]
  · simp [hf.isPos.nonneg_apply_self]
  · simp [charFun_eq_charFunDual_toDualMap, h]
  · simp [hf.isSymm.map_symm]
  · simp [hf.isPos.nonneg_apply_self]
  · simp [← charFun_toDual_symm_eq_charFunDual, h]

/-- If the characteristic function of `μ` takes the form of a gaussian characteristic function,
then the parameters have to be the expectation and the covariance bilinear form. -/
@[blueprint
  "lem:isGaussian_iff_gaussian_charFun"
  (statement := /-- A finite measure $\mu$ on $E$ is Gaussian if and only if there exists $m \in E$
    and $C$ positive semidefinite such that for all $t \in E$, the characteristic function of $\mu$
    at $t$ is
    \begin{align*}
      \hat{\mu}(t) = \exp\left(i \langle t, m \rangle - \frac{1}{2} C(t, t)\right) \: ,
    \end{align*}
    If that's the case, then $m = m_\mu$ and $C = C'_\mu$. -/)
  (proof := /-- Lemma~\ref{lem:IsGaussian.charFun_eq} states that the characteristic function of a
    Gaussian measure has the wanted form.
    
    Suppose now that there exists $m \in E$ and $C$ positive semidefinite such that for all $t \in
    E$, $\hat{\mu}(t) = \exp\left(i \langle t, m \rangle - \frac{1}{2} C(t, t)\right)$.
    
    We need to show that for all $L \in E^*$, $L_*\mu$ is a Gaussian measure on $\mathbb{R}$.
    Such an $L$ can be written as $\langle u, \cdot \rangle$ for some $u \in E$.
    Let then $u \in E$. We compute the characteristic function of $\langle u, \cdot\rangle_*\mu$ at
    $x \in \mathbb{R}$ with Lemma~\ref{lem:charFun_map_eq_charFunDual_smul}:
    \begin{align*}
      \widehat{\langle u, \cdot\rangle_*\mu}(x)
      &= \hat{\mu}(x \cdot u)
      \\
      &= \exp\left(i x \langle u, m \rangle - \frac{1}{2} x^2 C(u, u)\right)
      \: .
    \end{align*}
    This is the characteristic function of a Gaussian measure on $\mathbb{R}$ with mean $\langle u,
    m \rangle$ and variance $C(u, u)$.
    By Theorem~\ref{thm:ext_of_charFun}, $\langle u, \cdot\rangle_*\mu$ is Gaussian, hence $\mu$ is
    Gaussian.
    
    By Lemma~\ref{lem:IsGaussian.charFun_eq}, we deduce that for any $t \in E$ we have
    $$\exp\left(i\langle t, m \rangle - \frac{1}{2} C(t, t)\right) = \exp\left(i\langle t, m_\mu
    \rangle - \frac{1}{2} C'_\mu(t, t)\right).$$
    In particular, for any $t$ there exists $n_t \in \mathbb{Z}$ such that
    $$i\langle t, m \rangle - \frac{1}{2} C(t, t) = i\langle t, m_\mu \rangle - \frac{1}{2}
    C'_\mu(t, t) + 2i\pi n_t.$$
    We deduce that $n$ is a continuous map from $E$ to $\mathbb{Z}$, and thus must be constant
    because $E$ is connected. By looking at the value at $t = 0$, we deduce that for any $t$, $n_t =
    0$. Looking at real and imaginary parts we obtain that for any $t$,
    $$\langle t, m \rangle = \langle t, m_\mu \rangle \quad \text{and} \quad C(t, t) = C'_\mu(t,
    t).$$
    We immediately deduce that $m = m_\mu$. Moreover, because $C$ and $C'_\mu$ are symmetric, they
    are characterized by their values on the diagonal. Indeed, for any $x, y$,
    $$C(x, y) = \frac{1}{2} (C(x + y, x + y) - C(x, x) - C(y, y)).$$
    We deduce that $C = C'_\mu$. -/)
  (latexEnv := "lemma")]
lemma gaussian_charFun_congr [IsFiniteMeasure μ] (m : E) (f : ContinuousBilinForm ℝ E)
    (hf : f.IsPosSemidef) (h : ∀ t, charFun μ t = exp (⟪t, m⟫_ℝ * I - f t t / 2)) :
    m = ∫ x, x ∂μ ∧ f = covInnerBilin μ := by
  let g : ContinuousBilinForm ℝ (StrongDual ℝ E) :=
    f.bilinearComp (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
      (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
  have : ∀ L : StrongDual ℝ E, charFunDual μ L = exp (L m * I - g L L / 2) := by
    simp [← charFun_toDual_symm_eq_charFunDual, h, g]
  have hg : g.IsPosSemidef := by
    refine ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩
    · simp [g, hf.isSymm.map_symm]
    · simp [g, hf.isPos.nonneg_apply_self]
  have := gaussian_charFunDual_congr hg this
  refine ⟨this.1, ?_⟩
  ext
  simp [covInnerBilin, ← this.2, g, ← InnerProductSpace.toDual_apply_eq_toDualMap_apply]

/-- Two Gaussian measures are equal if they have same mean and same covariance. This is
`IsGaussian.ext_covarianceBilinDual` specialized to Hilbert spaces. -/
@[blueprint
  "lem:IsGaussian.ext_iff"
  (statement := /-- Two Gaussian measures $\mu$ and $\nu$ on a separable Hilbert space are equal if
    and only if they have same mean and same covariance. -/)
  (proof := /-- The forward direction is immediate.
    
    For the converse direction, it is enough to show that $\mu$ and $\nu$ have the same
    characteristic function by Theorem~\ref{thm:ext_of_charFun}. As they are both Gaussian, their
    characteristic functions only depend on their mean and covariance by
    Lemma~\ref{lem:IsGaussian.charFun_eq}. Thus they are equal. -/)
  (latexEnv := "lemma")]
protected lemma IsGaussian.ext {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covInnerBilin μ = covInnerBilin ν) : μ = ν := by
  apply Measure.ext_of_charFun
  ext t
  simp_rw [IsGaussian.charFun_eq, hm, hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. This is
`IsGaussian.ext_iff_covarianceBilinDual` specialized to Hilbert spaces. -/
@[blueprint
  "lem:IsGaussian.ext_iff"
  (statement := /-- Two Gaussian measures $\mu$ and $\nu$ on a separable Hilbert space are equal if
    and only if they have same mean and same covariance. -/)
  (proof := /-- The forward direction is immediate.
    
    For the converse direction, it is enough to show that $\mu$ and $\nu$ have the same
    characteristic function by Theorem~\ref{thm:ext_of_charFun}. As they are both Gaussian, their
    characteristic functions only depend on their mean and covariance by
    Lemma~\ref{lem:IsGaussian.charFun_eq}. Thus they are equal. -/)
  (latexEnv := "lemma")]
protected lemma IsGaussian.ext_iff {ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covInnerBilin μ = covInnerBilin ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext h.1 h.2

end InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- Two Gaussian measures are equal if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_covarianceBilin {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covarianceBilinDual μ = covarianceBilinDual ν) : μ = ν := by
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [IsGaussian.charFunDual_eq, integral_complex_ofReal,
    L.integral_comp_id_comm' IsGaussian.integrable_id, hm,
    ← covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id, hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_iff_covarianceBilin {ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covarianceBilinDual μ = covarianceBilinDual ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext_covarianceBilin h.1 h.2

lemma IsGaussian.eq_gaussianReal (μ : Measure ℝ) [IsGaussian μ] :
    μ = gaussianReal μ[id] Var[id; μ].toNNReal := by
  nth_rw 1 [← Measure.map_id (μ := μ), ← ContinuousLinearMap.coe_id' (R₁ := ℝ),
    map_eq_gaussianReal]
  rfl

lemma HasGaussianLaw.map_eq_gaussianReal {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} [HasGaussianLaw X P] :
    P.map X = gaussianReal P[X] Var[X; P].toNNReal := by
  rw [IsGaussian.eq_gaussianReal (.map _ _), integral_map, variance_map]
  · rfl
  any_goals fun_prop

lemma HasGaussianLaw.charFun_map_real {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} [HasGaussianLaw X P] (t : ℝ) :
    charFun (P.map X) t = exp (t * P[X] * I - t ^ 2 * Var[X; P] / 2) := by
  rw [HasGaussianLaw.map_eq_gaussianReal, IsGaussian.charFun_eq, covInnerBilin_real_self]
  · simp [variance_nonneg, integral_complex_ofReal, mul_comm]
  exact IsGaussian.memLp_two_id

end ProbabilityTheory
