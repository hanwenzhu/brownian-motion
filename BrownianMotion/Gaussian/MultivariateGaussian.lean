/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Architect
import BrownianMotion.Gaussian.Gaussian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Matrix.Order



/-!
# Multivariate Gaussian distributions
-/

open MeasureTheory ProbabilityTheory Filter Matrix NormedSpace WithLp
open scoped ENNReal NNReal Topology RealInnerProductSpace MatrixOrder

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  {d : ℕ}

variable (E) in
/-- Standard Gaussian distribution on `E`. -/
@[blueprint
  "def:stdGaussian"
  (title := "Standard Gaussian measure")
  (statement := /-- Let $(e_1, \ldots, e_d)$ be an orthonormal basis of $E$ and let $\mu$ be the
    standard Gaussian measure on $\mathbb{R}$.
    The standard Gaussian measure on $E$ is the pushforward measure of the product measure $\mu
    \times \ldots \times \mu$ by the map $x \mapsto \sum_{i=1}^d x_i \cdot e_i$. -/)]
noncomputable
def stdGaussian : Measure E :=
  (Measure.pi (fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 1)).map
    (fun x ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i)

variable [BorelSpace E]

@[blueprint
  "lem:isProbabilityMeasure_stdGaussian"
  (statement := /-- The standard Gaussian measure is a probability measure. -/)
  (latexEnv := "lemma")]
instance isProbabilityMeasure_stdGaussian : IsProbabilityMeasure (stdGaussian E) :=
    Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

@[simp, blueprint
  "lem:integral_id_stdGaussian"
  (statement := /-- The mean of the standard Gaussian measure is $0$. -/)
  (latexEnv := "lemma")]
lemma integral_id_stdGaussian : ∫ x, x ∂(stdGaussian E) = 0 := by
  rw [stdGaussian, integral_map _ (by fun_prop)]
  swap; · exact (Finset.measurable_sum _ (by fun_prop)).aemeasurable -- todo: add fun_prop tag
  rw [integral_finset_sum]
  swap
  · refine fun i _ ↦ Integrable.smul_const ?_ _
    convert integrable_comp_eval (i := i) (f := id) ?_
    · infer_instance
    · rw [← memLp_one_iff_integrable]
      exact memLp_id_gaussianReal 1
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have : (∫ (a : Fin (Module.finrank ℝ E) → ℝ), a i ∂Measure.pi fun x ↦ gaussianReal 0 1)
      = ∫ x, x ∂gaussianReal 0 1 := by
    convert integral_comp_eval (i := i) aestronglyMeasurable_id
    all_goals infer_instance
  simp [integral_smul_const, this]

attribute [blueprint
  "lem:integral_eval_pi"
  (statement := /-- For $\mu_1, \ldots, \mu_d$ probability measures on $\mathbb{R}$ and $f :
    \mathbb{R} \to \mathbb{R}$ integrable with respect to $\mu_i$, we have
    \begin{align*}
      \int_x f(x_i) \, d(\mu_1 \times \ldots \times \mu_d)(x)
      = \int_x f(x) \, d\mu_i
      \: .
    \end{align*} -/)
  (proof := /-- As $f$ is integrable, we can use Fubini theorem to obtain that
    $$\int f(x_i) \, d(\mu_1 \times \ldots \times \mu_d)(x) = \int f(x) \, d\mu_i(x) \times \prod_{j
    \ne i} \int 1 \, d\mu_j(x) = \int f(x) \, d\mu_i(x)$$
    because the $\mu_j$s are probability measures. -/)
  (latexEnv := "lemma")]
  MeasureTheory.integral_comp_eval

@[blueprint
  "lem:isCentered_stdGaussian"
  (statement := /-- The standard Gaussian measure on $E$ is centered, i.e., $\mu[L] = 0$ for every
    $L \in E^*$. -/)
  (latexEnv := "lemma")]
lemma isCentered_stdGaussian : ∀ L : StrongDual ℝ E, (stdGaussian E)[L] = 0 := by
  intro L
  rw [L.integral_comp_id_comm, integral_id_stdGaussian, map_zero]
  rw [stdGaussian, integrable_map_measure]
  · rw [Function.id_comp]
    exact integrable_finset_sum _ fun i _ ↦ Integrable.smul_const
      (integrable_comp_eval (f := id) IsGaussian.integrable_id) _
  · exact aestronglyMeasurable_id
  · exact Measurable.aemeasurable (by fun_prop)

lemma variance_dual_stdGaussian (L : StrongDual ℝ E) : Var[L; stdGaussian E] = ‖L‖ ^ 2 := by
  rw [stdGaussian, variance_map]
  · have : L ∘ (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i) =
        ∑ i, (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ L (stdOrthonormalBasis ℝ E i) * x i) := by
      ext x; simp [mul_comm]
    rw [this, variance_pi]
    · change ∑ i, Var[fun x ↦ _ * (id x); gaussianReal 0 1] = _
      simp_rw [variance_mul, variance_id_gaussianReal, (stdOrthonormalBasis ℝ E).norm_dual]
      simp
    · exact fun i ↦ IsGaussian.memLp_two_id.const_mul _
  · exact L.continuous.aemeasurable
  · exact Measurable.aemeasurable (by fun_prop)

attribute [blueprint
  "lem:charFun_gaussianReal"
  (statement := /-- The characteristic function of a real Gaussian measure with mean $\mu$ and
    variance $\sigma^2$ is given by
    $x \mapsto \exp\left(i \mu x - \frac{\sigma^2 x^2}{2}\right)$. -/)
  (latexEnv := "lemma")]
  ProbabilityTheory.charFun_gaussianReal

@[blueprint
  "lem:charFun_stdGaussian"
  (statement := /-- The characteristic function of the standard Gaussian measure on $E$ is given by
    \begin{align*}
      \hat{\mu}(t) = \exp\left(-\frac{1}{2} \Vert t \Vert^2 \right) \: .
    \end{align*} -/)
  (proof := /-- Denote by $\nu$ the standard Gaussian measure on $\mathbb{R}$. This is a
    straightforward computation:
    \begin{align*}
      \hat{\mu}(t) = \int \exp\left(i\langle t, \sum_{j=1}^d x_j \cdot e_j \rangle\right) d(\nu
      \times \ldots \times \nu)(dx) &= \int \exp\left(\sum_{j=1}^d ix_j\langle t, e_j \rangle\right)
      d(\nu \times \ldots \times \nu)(dx) \\
      &= \int \prod_{j=1}^d \exp\left(ix_j\langle t, e_j \rangle\right) d(\nu \times \ldots \times
      \nu)(dx) \\
      &= \prod_{j=1}^d \int \exp\left(ix\langle t, e_j \rangle\right) d\nu(x) \\
      &= \prod_{j=1}^d \exp\left(-\frac{\langle t, e_j \rangle^2}{2}\right) \\
      &= \exp\left(-\frac{1}{2} \Vert t \Vert^2 \right).
    \end{align*} -/)
  (latexEnv := "lemma")]
lemma charFun_stdGaussian (t : E) : charFun (stdGaussian E) t = Complex.exp (- ‖t‖ ^ 2 / 2) := by
  rw [charFun_apply, stdGaussian, integral_map]
  · simp_rw [sum_inner, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum,
      integral_fintype_prod_eq_prod
        (f := fun i x ↦ Complex.exp (⟪x • stdOrthonormalBasis ℝ E i, t⟫ * Complex.I)),
      real_inner_smul_left, mul_comm _ (⟪_, _⟫), Complex.ofReal_mul, ← charFun_apply_real,
      charFun_gaussianReal]
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one, one_mul,
      zero_sub]
    simp_rw [← Complex.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, ← Complex.ofReal_pow,
      ← Complex.ofReal_sum, ← (stdOrthonormalBasis ℝ E).norm_sq_eq_sum_sq_inner_right, neg_div]
  · exact Measurable.aemeasurable (by fun_prop)
  · exact Measurable.aestronglyMeasurable (by fun_prop)

@[blueprint
  "lem:isGaussian_stdGaussian"
  (statement := /-- The standard Gaussian measure on $E$ is a Gaussian measure. -/)
  (proof := /-- Since the standard Gaussian is a probability measure (hence finite), we can apply
    Lemma~\ref{lem:isGaussian_iff_gaussian_charFun} that states that it suffices to show that the
    characteristic function has a particular form.
    That form is given by Lemma~\ref{lem:charFun_stdGaussian}, taking $m=0$ and $C = \langle\cdot,
    \cdot\rangle$. -/)
  (latexEnv := "lemma")]
instance isGaussian_stdGaussian : IsGaussian (stdGaussian E) := by
  refine isGaussian_iff_gaussian_charFun.2 ?_
  use 0, ContinuousBilinForm.inner E, ContinuousBilinForm.isPosSemidef_inner
  simp [charFun_stdGaussian, neg_div]

lemma charFunDual_stdGaussian (L : StrongDual ℝ E) :
    charFunDual (stdGaussian E) L = Complex.exp (- ‖L‖ ^ 2 / 2) := by
  rw [IsGaussian.charFunDual_eq, integral_complex_ofReal, isCentered_stdGaussian,
    variance_dual_stdGaussian]
  simp [neg_div]

lemma covInnerBilin_stdGaussian :
    covInnerBilin (stdGaussian E) = ContinuousBilinForm.inner E := by
  refine gaussian_charFun_congr 0 _ ContinuousBilinForm.isPosSemidef_inner (fun t ↦ ?_) |>.2.symm
  simp [charFun_stdGaussian, neg_div]

@[blueprint
  "lem:covMatrix_stdGaussian"
  (statement := /-- The covariance matrix of the standard Gaussian measure is the identity matrix.
    -/)
  (proof := /-- From Lemma~\ref{lem:charFun_stdGaussian}, we know that for all $t \in \mathbb{R}$,
    $$\hat{\mu}(t) = \exp\left(-\frac{\|t\|^2}{2}\right) = \exp\left(-\frac{\langle t,
    \mathrm{I}t\rangle}{2}\right).$$
    As the identity is positive semidefinite, we deduce from
    Lemma~\ref{lem:isGaussian_iff_gaussian_charFun} that $\Sigma_\mu$ is the identity matrix. -/)
  (latexEnv := "lemma")]
lemma covMatrix_stdGaussian : covMatrix (stdGaussian E) = 1 := by
  rw [covMatrix, covInnerBilin_stdGaussian, ContinuousBilinForm.inner_toMatrix_eq_one]

lemma stdGaussian_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] (f : E ≃ₗᵢ[ℝ] F) :
    haveI := f.finiteDimensional; (stdGaussian E).map f = stdGaussian F := by
  have := f.finiteDimensional
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [← f.coe_coe_eq_coe, charFunDual_map, charFunDual_stdGaussian,
    L.opNorm_comp_linearIsometryEquiv]

lemma pi_eq_stdGaussian {n : Type*} [Fintype n] :
    (Measure.pi (fun _ ↦ gaussianReal 0 1)).map (toLp 2) = stdGaussian (EuclideanSpace ℝ n) := by
  -- This instance is not found automatically, probably a defeq issue between
  -- `n → ℝ` and `EuclideanSpace ℝ n`.
  have : IsFiniteMeasure (Measure.pi fun _ : n ↦ gaussianReal 0 1) := inferInstance
  apply Measure.ext_of_charFun (E := EuclideanSpace ℝ n)
  ext t
  simp_rw [charFun_stdGaussian, charFun_pi, charFun_gaussianReal, ← Complex.exp_sum,
    ← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq]
  simp [Finset.sum_div, neg_div]

lemma stdGaussian_eq_pi_map_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    stdGaussian E = (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map
      (fun x ↦ ∑ i, x i • b i) := by
  have : (fun (x : ι → ℝ) ↦ ∑ i, x i • b i) =
      ⇑((EuclideanSpace.basisFun ι ℝ).equiv b (Equiv.refl ι)) ∘ (toLp 2) := by
    simp_rw [← b.equiv_apply_euclideanSpace]
    rfl
  rw [this, ← Measure.map_map, pi_eq_stdGaussian, stdGaussian_map]
  all_goals fun_prop

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multivariate Gaussian measure on `EuclideanSpace ℝ ι` with mean `μ` and covariance
matrix `S`. -/
@[blueprint
  "def:multivariateGaussian"
  (title := "Multivariate Gaussian")
  (statement := /-- The multivariate Gaussian measure on $\mathbb{R}^d$ with mean $m \in
    \mathbb{R}^d$ and covariance matrix $\Sigma \in \mathbb{R}^{d \times d}$, with $\Sigma$ positive
    semidefinite, is the pushforward measure of the standard Gaussian measure on $\mathbb{R}^d$ by
    the map $x \mapsto m + \Sigma^{1/2} x$.
    We denote this measure by $\mathcal{N}(m, \Sigma)$. -/)]
noncomputable
def multivariateGaussian (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  (stdGaussian (EuclideanSpace ℝ ι)).map (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)

variable {μ : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} {hS : S.PosSemidef}

attribute [blueprint
  "lem:isGaussian_map"
  (statement := /-- Let $F, G$ be two Banach spaces, let $\mu$ be a Gaussian measure on $F$ and let
    $T : F \to G$ be a continuous linear map.
    Then $T_*\mu$ is a Gaussian measure on $G$. -/)
  (latexEnv := "lemma")]
  ProbabilityTheory.isGaussian_map

@[blueprint
  "lem:isGaussian_multivariateGaussian"
  (statement := /-- A multivariate Gaussian measure is a Gaussian measure. -/)
  (proof := /-- The multivariate Gaussian measure is the pushforward of the standard Gaussian
    measure by an affine map, and is thus Gaussian by Lemma~\ref{lem:isGaussian_add_const} and
    Lemma~\ref{lem:isGaussian_map}. -/)
  (latexEnv := "lemma")]
instance isGaussian_multivariateGaussian : IsGaussian (multivariateGaussian μ S) := by
  have h : (fun x ↦ μ + x) ∘ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))) =
    (fun x ↦ μ + (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) x) := rfl
  simp only [multivariateGaussian]
  rw [← h, ← Measure.map_map (measurable_const_add μ) (by measurability)]
  infer_instance

@[simp, blueprint
  "lem:integral_id_multivariateGaussian"
  (statement := /-- The mean of the multivariate Gaussian measure $\mathcal{N}(m, \Sigma)$ is $m$.
    -/)
  (latexEnv := "lemma")]
lemma integral_id_multivariateGaussian : ∫ x, x ∂(multivariateGaussian μ S) = μ := by
  rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop),
    integral_add (integrable_const _), integral_const]
  · simp [ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_fun_id]
  · exact IsGaussian.integrable_id.comp_measurable (by fun_prop)

lemma inner_toEuclideanCLM (x y : EuclideanSpace ℝ ι) :
    ⟪x, toEuclideanCLM (𝕜 := ℝ) S y⟫
      = (EuclideanSpace.basisFun ι ℝ).toBasis.repr x ⬝ᵥ S
        *ᵥ (EuclideanSpace.basisFun ι ℝ).toBasis.repr y := by
  simp only [toEuclideanCLM, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearEquiv.invFun_eq_symm, LinearMap.coe_toContinuousLinearMap_symm, StarAlgEquiv.trans_apply,
    LinearMap.toMatrixOrthonormal_symm_apply, LinearMap.toMatrix_symm, StarAlgEquiv.coe_mk,
    StarRingEquiv.coe_mk, RingEquiv.coe_mk, Equiv.coe_fn_mk, LinearMap.coe_toContinuousLinearMap',
    toLin_apply, mulVec_eq_sum, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply,
    smul_eq_mul, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, dotProduct]
  congr with i
  rw [mul_comm, ← WithLp.linearEquiv_apply 2 ℝ]
  simp [-EuclideanSpace.ofLp_single, Finset.sum_apply]

@[blueprint
  "lem:covMatrix_multivariateGaussian"
  (statement := /-- The covariance matrix of the multivariate Gaussian measure $\mathcal{N}(m,
    \Sigma)$ is $\Sigma$. -/)
  (latexEnv := "lemma")]
lemma covInnerBilin_multivariateGaussian (hS : S.PosSemidef) :
    covInnerBilin (multivariateGaussian μ S)
      = ContinuousBilinForm.ofMatrix S (EuclideanSpace.basisFun ι ℝ).toBasis := by
  have h : (fun x ↦ μ + x) ∘ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))) =
    (fun x ↦ μ + (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) x) := rfl
  simp only [multivariateGaussian]
  rw [← h, ← Measure.map_map (measurable_const_add μ) (by fun_prop)]
  rw [covInnerBilin_map_const_add]
  swap; · exact IsGaussian.memLp_two_id
  ext x y
  rw [covInnerBilin_map, covInnerBilin_stdGaussian]
  swap; · exact IsGaussian.memLp_two_id
  rw [ContinuousBilinForm.inner_apply, ContinuousBilinForm.ofMatrix_apply,
    ContinuousLinearMap.adjoint_inner_left]
  rw [IsSelfAdjoint.adjoint_eq]
  swap
  · unfold _root_.IsSelfAdjoint
    rw [← map_star, EmbeddingLike.apply_eq_iff_eq]
    simpa using (CFC.sqrt_nonneg S).isHermitian
  calc ⟪x, (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) y)⟫
  _ = ⟪x, toEuclideanCLM (𝕜 := ℝ) S y⟫ := by
    congr 1
    have : (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).comp (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))
        = toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt S) * (CFC.sqrt S)) := by
      rw [map_mul]
      rfl
    rw [CFC.sqrt_mul_sqrt_self _ hS.nonneg, ContinuousLinearMap.ext_iff] at this
    rw [← this y]
    simp
  _ = ((EuclideanSpace.basisFun ι ℝ).toBasis.repr x) ⬝ᵥ
      S *ᵥ ((EuclideanSpace.basisFun ι ℝ).toBasis.repr y) := inner_toEuclideanCLM _ _

lemma covariance_eval_multivariateGaussian (hS : S.PosSemidef) (i j : ι) :
    cov[fun x ↦ x i, fun x ↦ x j; multivariateGaussian μ S] = S i j := by
  have (i : ι) : (fun x : EuclideanSpace ℝ ι ↦ x i) =
      fun x ↦ ⟪EuclideanSpace.basisFun ι ℝ i, x⟫ := by ext; simp [PiLp.inner_apply]
  rw [this, this, ← covInnerBilin_apply_eq, covInnerBilin_multivariateGaussian hS,
    ContinuousBilinForm.ofMatrix_orthonormalBasis]
  exact IsGaussian.memLp_two_id

lemma variance_eval_multivariateGaussian (hS : S.PosSemidef) (i : ι) :
    Var[fun x ↦ x i; multivariateGaussian μ S] = S i i := by
  rw [← covariance_self, covariance_eval_multivariateGaussian hS]
  exact Measurable.aemeasurable <| by fun_prop

lemma hasLaw_eval_multivariateGaussian (hS : S.PosSemidef) {i : ι} :
    HasLaw (fun x ↦ x i) (gaussianReal (μ i) (S i i).toNNReal) (multivariateGaussian μ S) where
  aemeasurable := Measurable.aemeasurable (by fun_prop)
  map_eq := by
    rw [← EuclideanSpace.coe_proj ℝ, IsGaussian.map_eq_gaussianReal,
      ContinuousLinearMap.integral_comp_id_comm, integral_id_multivariateGaussian,
      EuclideanSpace.proj_apply, EuclideanSpace.coe_proj, variance_eval_multivariateGaussian hS]
    exact IsGaussian.integrable_id

@[blueprint
  "thm:charFun_multivariateGaussian"
  (statement := /-- The characteristic function of a multivariate Gaussian measure $\mathcal{N}(m,
    \Sigma)$ is given by
    \begin{align*}
      \hat{\mu}(t) = \exp\left(i \langle m, t \rangle - \frac{1}{2} \langle t, \Sigma t
      \rangle\right)
      \: .
    \end{align*} -/)
  (proof := /-- Since the multivariate Gaussian measure is a Gaussian measure, we can apply
    Lemma~\ref{lem:IsGaussian.charFun_eq} to it.
    It suffices then to show that the mean and the covariance matrix of the multivariate Gaussian
    measure are equal to $m$ and $\Sigma$, respectively.
    This is given by Lemma~\ref{lem:integral_id_multivariateGaussian} and
    Lemma~\ref{lem:covMatrix_multivariateGaussian}. -/)]
lemma charFun_multivariateGaussian (hS : S.PosSemidef) (x : EuclideanSpace ℝ ι) :
    charFun (multivariateGaussian μ S) x =
      Complex.exp (⟪x, μ⟫ * Complex.I
        - ContinuousBilinForm.ofMatrix S (EuclideanSpace.basisFun ι ℝ).toBasis x x / 2) := by
  rw [IsGaussian.charFun_eq]
  congr
  · exact integral_id_multivariateGaussian
  · exact covInnerBilin_multivariateGaussian hS

/-- `Finset.restrict₂` as a continuous linear map. -/
def _root_.Finset.restrict₂CLM {ι : Type*} (R : Type*) {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)]
    {I J : Finset ι} (hIJ : I ⊆ J) :
    (Π i : J, M i) →L[R] Π i : I, M i where
  toFun := Finset.restrict₂ hIJ
  map_add' x y := by ext; simp
  map_smul' m x := by ext; simp
  cont := by fun_prop

lemma _root_.Finset.coe_restrict₂CLM {ι R : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)] {I J : Finset ι}
    (hIJ : I ⊆ J) :
    ⇑(Finset.restrict₂CLM (R := R) (M := M) hIJ) = Finset.restrict₂ hIJ := rfl

@[simp]
lemma _root_.Finset.restrict₂CLM_apply {ι R : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)] {I J : Finset ι}
    (hIJ : I ⊆ J) (x : Π i : J, M i) (i : I) :
    Finset.restrict₂CLM (R := R) hIJ x i = x ⟨i.1, hIJ i.2⟩ := rfl

/-- The restriction from `EuclideanSpace 𝕜 J` to `EuclideanSpace κ I` when `I ⊆ J`. -/
def _root_.EuclideanSpace.restrict₂ {ι 𝕜 : Type*} [RCLike 𝕜] {I J : Finset ι} (hIJ : I ⊆ J) :
    EuclideanSpace 𝕜 J →L[𝕜] EuclideanSpace 𝕜 I :=
  (EuclideanSpace.equiv I 𝕜).symm.toContinuousLinearMap ∘L
    (Finset.restrict₂CLM 𝕜 (M := fun _ ↦ 𝕜) hIJ) ∘L
      (EuclideanSpace.equiv J 𝕜).toContinuousLinearMap

-- lemma _root_.EuclideanSpace.coe_restrict₂
--     {ι 𝕜 : Type*} [RCLike 𝕜] {I J : Finset ι} (hIJ : I ⊆ J) :
--     ⇑(@EuclideanSpace.restrict₂ ι 𝕜 _ I J hIJ) = EuclideanSpace.restrict₂ hIJ := rfl

@[simp]
lemma _root_.EuclideanSpace.restrict₂_apply {ι 𝕜 : Type*} [RCLike 𝕜] {I J : Finset ι}
    (hIJ : I ⊆ J) (x : EuclideanSpace 𝕜 J) (i : I) :
    EuclideanSpace.restrict₂ hIJ x i = x ⟨i.1, hIJ i.2⟩ := rfl

variable {ι : Type*} [DecidableEq ι] {I J : Finset ι}

variable {μ : EuclideanSpace ℝ I} {S : Matrix I I ℝ} {hS : S.PosSemidef}

lemma measurePreserving_restrict_multivariateGaussian (hS : S.PosSemidef) (hJI : J ⊆ I) :
    MeasurePreserving (EuclideanSpace.restrict₂ hJI) (multivariateGaussian μ S)
      (multivariateGaussian (μ.restrict₂ hJI)
      (S.submatrix (fun i : J ↦ ⟨i.1, hJI i.2⟩) (fun i : J ↦ ⟨i.1, hJI i.2⟩))) where
  measurable := by fun_prop
  map_eq := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian]
      exact IsGaussian.integrable_id
    apply ContinuousBilinForm.ext_basis (EuclideanSpace.basisFun J ℝ).toBasis
    intro i j
    rw [covInnerBilin_apply_eq, covariance_map]
    · have (i : J) : (fun u ↦ ⟪(EuclideanSpace.basisFun J ℝ).toBasis i, u⟫) ∘
          EuclideanSpace.restrict₂ hJI = fun u ↦ u ⟨i.1, hJI i.2⟩ := by ext; simp [PiLp.inner_apply]
      simp_rw [this, covariance_eval_multivariateGaussian hS,
        covInnerBilin_multivariateGaussian (hS.submatrix _),
        ContinuousBilinForm.ofMatrix_basis, S.submatrix_apply]
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

open scoped ComplexOrder in
lemma _root_.Matrix.PosSemidef.sqrt_one {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜] [DecidableEq n] :
    CFC.sqrt (1 : Matrix n n 𝕜) = 1 := by simp

lemma multivariateGaussian_zero_one [Fintype ι] :
    multivariateGaussian 0 (1 : Matrix ι ι ℝ) = stdGaussian (EuclideanSpace ℝ ι) := by
  simp [multivariateGaussian]

end ProbabilityTheory
