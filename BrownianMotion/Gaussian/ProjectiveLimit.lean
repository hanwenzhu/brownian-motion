/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Architect
import BrownianMotion.Auxiliary.NNReal
import BrownianMotion.Gaussian.MultivariateGaussian
import KolmogorovExtension4.KolmogorovExtension
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Pre-Brownian motion as a projective limit

-/

open MeasureTheory NormedSpace Set
open scoped ENNReal NNReal

namespace L2

variable {ι : Type*} [Fintype ι]
variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/- In an `L2` space, the matrix of intersections of pairs of sets is positive semi-definite. -/
theorem posSemidef_interMatrix {μ : Measure α} {v : ι → (Set α)}
    (hv₁ : ∀ j, MeasurableSet (v j)) (hv₂ : ∀ j, μ (v j) ≠ ∞ := by finiteness) :
    Matrix.PosSemidef (Matrix.of fun i j : ι ↦ μ.real (v i ∩ v j)) := by
  simp only [hv₁, ne_eq, hv₂, not_false_eq_true,
    ← L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]
  exact Matrix.posSemidef_gram ℝ _

end L2

namespace ProbabilityTheory

variable {ι : Type*} {d : ℕ}

def brownianCovMatrix (I : Finset ℝ≥0) : Matrix I I ℝ := Matrix.of fun s t ↦ min s.1 t.1

lemma brownianCovMatrix_apply {I : Finset ℝ≥0} (s t : I) :
    brownianCovMatrix I s t = min s.1 t.1 := rfl

lemma brownianCovMatrix_submatrix {I J : Finset ℝ≥0} (hJI : J ⊆ I) :
    (brownianCovMatrix I).submatrix (fun i : J ↦ ⟨i.1, hJI i.2⟩) (fun i : J ↦ ⟨i.1, hJI i.2⟩) =
    brownianCovMatrix J := rfl

attribute [blueprint
  "lem:posSemidef_gramMatrix"
  (statement := /-- A gram matrix is positive semidefinite. -/)
  (proof := /-- Symmetry is obvious from the definition.
    Let $x \in E$. Then
    \begin{align*}
      \langle x, G x \rangle
      &= \sum_{i,j} x_i x_j \langle v_i, v_j \rangle
      \\
      &= \langle \sum_i x_i v_i, \sum_j x_j v_j \rangle
      \\
      &= \left\Vert \sum_i x_i v_i \right\Vert^2
      \\
      &\ge 0
      \: .
    \end{align*} -/)
  (latexEnv := "lemma")]
  Matrix.posSemidef_gram

@[blueprint
  "lem:posSemidef_brownianCov"
  (statement := /-- For $I = \{t_1, \ldots, t_n\}$ a finite subset of $\mathbb{R}_+$, let $C \in
    \mathbb{R}^{n \times n}$ be the matrix $C_{ij} = \min(t_i, t_j)$ for $1 \leq i,j \leq n$.
    Then $C$ is positive semidefinite. -/)
  (proof := /-- $C$ is a Gram matrix by Lemma~\ref{lem:C_eq_gramMatrix}.
    By Lemma~\ref{lem:posSemidef_gramMatrix}, it is positive semidefinite. -/)
  (latexEnv := "lemma")]
lemma posSemidef_brownianCovMatrix (I : Finset ℝ≥0) :
    (brownianCovMatrix I).PosSemidef := by
  have h : brownianCovMatrix I =
      fun s t ↦ volume.real ((Icc 0 s.1.toReal) ∩ (Icc 0 t.1.toReal)) := by
    simp [Icc_inter_Icc, max_self, Real.volume_real_Icc, sub_zero, le_inf_iff,
      NNReal.zero_le_coe, and_self, sup_of_le_left]
    rfl
  exact h ▸ L2.posSemidef_interMatrix (fun j ↦ measurableSet_Icc)
    (fun j ↦ isCompact_Icc.measure_ne_top)

variable [DecidableEq ι]

@[blueprint
  "def:gaussianProjectiveFamily"
  (title := "Projective family of the Brownian motion")
  (statement := /-- For $I = \{t_1, \ldots, t_n\}$ a finite subset of $\mathbb{R}_+$, let $P^B_I$ be
    the multivariate Gaussian measure on $\mathbb{R}^n$ with mean $0$ and covariance matrix $C_{ij}
    = \min(t_i, t_j)$ for $1 \leq i,j \leq n$.
    We call the family of measures $P^B_I$ the \emph{projective family of the Brownian motion}. -/)]
noncomputable
def gaussianProjectiveFamily (I : Finset ℝ≥0) : Measure (I → ℝ) :=
  multivariateGaussian 0 (brownianCovMatrix I) |>.map (MeasurableEquiv.toLp 2 (I → ℝ)).symm

lemma measurePreserving_equiv_multivariateGaussian (I : Finset ℝ≥0) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (I → ℝ)).symm
      (multivariateGaussian 0 (brownianCovMatrix I)) (gaussianProjectiveFamily I) where
  measurable := by fun_prop
  map_eq := rfl

lemma measurePreserving_equiv_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (I → ℝ)).symm.symm (gaussianProjectiveFamily I)
      (multivariateGaussian 0 (brownianCovMatrix I)) where
  measurable := by fun_prop
  map_eq := by
    rw [gaussianProjectiveFamily, Measure.map_map, MeasurableEquiv.symm_comp_self,
      Measure.map_id]
    all_goals fun_prop

lemma integral_gaussianProjectiveFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Finset ℝ≥0) (f : (I → ℝ) → E) :
    ∫ x, f x ∂gaussianProjectiveFamily I =
      ∫ x, f (EuclideanSpace.equiv I ℝ x)
        ∂multivariateGaussian 0 (brownianCovMatrix I) := by
  simp [gaussianProjectiveFamily, integral_map_equiv]

instance isGaussian_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    IsGaussian (gaussianProjectiveFamily I) := by
  unfold gaussianProjectiveFamily
  rw [MeasurableEquiv.coe_toLp_symm_eq]
  infer_instance

@[simp]
lemma integral_id_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    ∫ x, x ∂(gaussianProjectiveFamily I) = 0 := by
  rw [integral_gaussianProjectiveFamily, ← ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
    integral_id_multivariateGaussian, map_zero]

lemma integral_id_gaussianProjectiveFamily' (I : Finset ℝ≥0) :
    ∫ x, id x ∂(gaussianProjectiveFamily I) = 0 := integral_id_gaussianProjectiveFamily I

open scoped RealInnerProductSpace in
lemma covariance_eval_gaussianProjectiveFamily (I : Finset ℝ≥0) (s t : I) :
    cov[fun x ↦ x s, fun x ↦ x t; gaussianProjectiveFamily I] = min s.1 t.1 := by
  rw [gaussianProjectiveFamily, covariance_map_equiv]
  change cov[fun x : EuclideanSpace ℝ I ↦ x s, fun x ↦ x t; _] = _
  have (u : I) : (fun x : EuclideanSpace ℝ I ↦ x u) =
      fun x ↦ ⟪EuclideanSpace.basisFun I ℝ u, x⟫ := by ext; simp [PiLp.inner_apply]
  rw [this, this, ← covInnerBilin_apply_eq,
    covInnerBilin_multivariateGaussian (posSemidef_brownianCovMatrix I),
    ContinuousBilinForm.ofMatrix_orthonormalBasis, brownianCovMatrix_apply]
  exact IsGaussian.memLp_two_id

lemma variance_eval_gaussianProjectiveFamily {I : Finset ℝ≥0} (s : I) :
    Var[fun x ↦ x s; gaussianProjectiveFamily I] = s := by
  rw [← covariance_self, covariance_eval_gaussianProjectiveFamily, min_self]
  exact Measurable.aemeasurable <| by fun_prop

lemma hasLaw_eval_gaussianProjectiveFamily {I : Finset ℝ≥0} (s : I) :
    HasLaw (fun x ↦ x s) (gaussianReal 0 s) (gaussianProjectiveFamily I) where
  aemeasurable := Measurable.aemeasurable <| by fun_prop
  map_eq := by
    rw [HasGaussianLaw.map_eq_gaussianReal, variance_eval_gaussianProjectiveFamily,
      Real.toNNReal_coe]
    conv => enter [1, 1, 2]; change fun x ↦ ContinuousLinearMap.proj (R := ℝ) s x
    rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_gaussianProjectiveFamily, map_zero]
    exact IsGaussian.integrable_id

open ContinuousLinearMap in
lemma hasLaw_eval_sub_eval_gaussianProjectiveFamily (I : Finset ℝ≥0) (s t : I) :
    HasLaw ((fun x ↦ x s - x t)) (gaussianReal 0 (max (s - t) (t - s)))
      (gaussianProjectiveFamily I) where
  map_eq := by
    rw [HasGaussianLaw.map_eq_gaussianReal, variance_fun_sub,
      variance_eval_gaussianProjectiveFamily, variance_eval_gaussianProjectiveFamily,
      covariance_eval_gaussianProjectiveFamily]
    · conv =>
        enter [1, 1, 2];
        change fun x ↦ (proj (R := ℝ) (φ := fun i : I ↦ ℝ) s -
          proj (R := ℝ) (φ := fun i : I ↦ ℝ) t) x
      rw [integral_comp_id_comm, integral_id_gaussianProjectiveFamily, map_zero]
      · norm_cast
        rw [sub_add_eq_add_sub, ← NNReal.coe_add, ← NNReal.coe_sub, Real.toNNReal_coe,
          NNReal.add_sub_two_mul_min_eq_max]
        nth_grw 1 [two_mul, min_le_left, min_le_right]
      · exact IsGaussian.integrable_id
    any_goals exact HasGaussianLaw.memLp_two

@[blueprint
  "lem:isProjectiveMeasureFamily_gaussianProjectiveFamily"
  (statement := /-- The projective family of the Brownian motion is a projective family of measures.
    -/)
  (proof := /-- Let $J \subseteq I$ be finite subsets of $\mathbb{R}_+$.
    We need to show that the restriction from $\mathbb{R}^I$ to $\mathbb{R}^J$ (denote it by
    $\pi_{IJ}$) maps $P^B_I$ to $P^B_J$.
    
    The restriction is a continuous linear map from $\mathbb{R}^I$ to $\mathbb{R}^J$.
    The map of a Gaussian measure by a continuous linear map is Gaussian
    (Lemma~\ref{lem:isGaussian_map}).
    It thus suffices to show that the mean and covariance matrix of the map are equal to the ones of
    $P^B_J$ by Lemma~\ref{lem:IsGaussian.ext_iff}.
    
    The mean of the map is $0$, since the mean of $P^B_I$ is $0$ and the map is linear.
    
    Let us turn to the covariance matrix. For any $i \in J$, the map $x : \mathbb{R}^I \mapsto
    \pi_{IJ}(x) i$ is equal to $x : \mathbb{R}^I \mapsto x i$. Let $i, j \in J$. The covariance of
    $x : \mathbb{R}^J \mapsto x i$ and $x : \mathbb{R}^J \mapsto x j$ with respect to
    ${\pi_{IJ}}_*P^B_J$ is equal to the covariance of $x : \mathbb{R}^I \mapsto \pi_{IJ}(x) i$ and
    $x : \mathbb{R}^I \mapsto \pi_{IJ}(x) j$ with respect to $P^B_I$, which is equal to the
    covariance of $x : \mathbb{R}^I \mapsto x i$ and $x : \mathbb{R}^I \mapsto x i$ with respect to
    $P^B_I$, which is equal to $t_i \land t_j$. But this is also the covariance of $x : \mathbb{R}^J
    \mapsto x i$ and $x : \mathbb{R}^J \mapsto x j$ with respect to $P^B_J$, so we are done. -/)
  (latexEnv := "lemma")]
lemma isProjectiveMeasureFamily_gaussianProjectiveFamily :
    IsProjectiveMeasureFamily (α := fun _ ↦ ℝ) gaussianProjectiveFamily := by
  intro I J hJI
  nth_rw 2 [gaussianProjectiveFamily]
  rw [Measure.map_map]
  · have : (Finset.restrict₂ (π := fun _ ↦ ℝ) hJI ∘ (MeasurableEquiv.toLp 2 (I → ℝ)).symm) =
        (MeasurableEquiv.toLp 2 (J → ℝ)).symm ∘ (EuclideanSpace.restrict₂ hJI) := by
      ext; simp
    rw [this, ((measurePreserving_equiv_multivariateGaussian J).comp
      (measurePreserving_restrict_multivariateGaussian
        (posSemidef_brownianCovMatrix I) hJI)).map_eq]
  · exact Finset.measurable_restrict₂ _ -- fun_prop fails
  · fun_prop

lemma measurePreserving_restrict_gaussianProjectiveFamily {I J : Finset ℝ≥0} (hIJ : I ⊆ J) :
    MeasurePreserving (Finset.restrict₂ (π := fun _ ↦ ℝ) hIJ) (gaussianProjectiveFamily J)
      (gaussianProjectiveFamily I) where
  measurable := Finset.measurable_restrict₂ _
  map_eq := isProjectiveMeasureFamily_gaussianProjectiveFamily J I hIJ |>.symm

attribute [blueprint
  "def:IsProjectiveMeasureFamily"
  (title := "Projective family")
  (statement := /-- A family of measures $P$ indexed by finite sets of $T$ is projective if, for
    finite sets $J \subseteq I$, the projection from $E^I$ to $E^J$ maps $P_I$ to $P_J$. -/)]
  MeasureTheory.IsProjectiveMeasureFamily

attribute [blueprint
  "def:IsProjectiveLimit"
  (title := "Projective limit")
  (statement := /-- A measure $\mu$ on $E^T$ is the projective limit of a projective family of
    measures $P$ indexed by finite sets of $T$ if, for every finite set $I \subseteq T$, the
    projection from $E^T$ to $E^I$ maps $\mu$ to $P_I$. -/)]
  MeasureTheory.IsProjectiveLimit

attribute [blueprint
  "thm:kolmogorovExtension"
  (title := "Kolmogorov extension theorem")
  (statement := /-- Let $\mathcal{X}$ be a Polish space, equipped with the Borel $\sigma$-algebra,
    and let $T$ be an index set.
    Let $P$ be a projective family of finite measures on $\mathcal{X}$.
    Then the projective limit $\mu$ of $P$ exists, is unique, and is a finite measure on
    $\mathcal{X}^T$.
    Moreover, if $P_I$ is a probability measure for every finite set $I \subseteq T$, then $\mu$ is
    a probability measure. -/)]
  MeasureTheory.projectiveLimit

attribute [blueprint
  "thm:kolmogorovExtension"
  (title := "Kolmogorov extension theorem")
  (statement := /-- Let $\mathcal{X}$ be a Polish space, equipped with the Borel $\sigma$-algebra,
    and let $T$ be an index set.
    Let $P$ be a projective family of finite measures on $\mathcal{X}$.
    Then the projective limit $\mu$ of $P$ exists, is unique, and is a finite measure on
    $\mathcal{X}^T$.
    Moreover, if $P_I$ is a probability measure for every finite set $I \subseteq T$, then $\mu$ is
    a probability measure. -/)]
  MeasureTheory.IsProjectiveLimit.unique

attribute [blueprint
  "thm:kolmogorovExtension"
  (title := "Kolmogorov extension theorem")
  (statement := /-- Let $\mathcal{X}$ be a Polish space, equipped with the Borel $\sigma$-algebra,
    and let $T$ be an index set.
    Let $P$ be a projective family of finite measures on $\mathcal{X}$.
    Then the projective limit $\mu$ of $P$ exists, is unique, and is a finite measure on
    $\mathcal{X}^T$.
    Moreover, if $P_I$ is a probability measure for every finite set $I \subseteq T$, then $\mu$ is
    a probability measure. -/)]
  MeasureTheory.isProjectiveLimit_projectiveLimit

attribute [blueprint
  "thm:kolmogorovExtension"
  (title := "Kolmogorov extension theorem")
  (statement := /-- Let $\mathcal{X}$ be a Polish space, equipped with the Borel $\sigma$-algebra,
    and let $T$ be an index set.
    Let $P$ be a projective family of finite measures on $\mathcal{X}$.
    Then the projective limit $\mu$ of $P$ exists, is unique, and is a finite measure on
    $\mathcal{X}^T$.
    Moreover, if $P_I$ is a probability measure for every finite set $I \subseteq T$, then $\mu$ is
    a probability measure. -/)]
  MeasureTheory.isFiniteMeasure_projectiveLimit

attribute [blueprint
  "thm:kolmogorovExtension"
  (title := "Kolmogorov extension theorem")
  (statement := /-- Let $\mathcal{X}$ be a Polish space, equipped with the Borel $\sigma$-algebra,
    and let $T$ be an index set.
    Let $P$ be a projective family of finite measures on $\mathcal{X}$.
    Then the projective limit $\mu$ of $P$ exists, is unique, and is a finite measure on
    $\mathcal{X}^T$.
    Moreover, if $P_I$ is a probability measure for every finite set $I \subseteq T$, then $\mu$ is
    a probability measure. -/)]
  MeasureTheory.isProbabilityMeasure_projectiveLimit

@[blueprint
  "def:gaussianLimit"
  (statement := /-- We denote by $P_B$ the projective limit of the projective family of the Brownian
    motion given by Theorem~\ref{thm:kolmogorovExtension}.
    This is a probability measure on $\mathbb{R}^{\mathbb{R}_+}$. -/)]
noncomputable
def gaussianLimit : Measure (ℝ≥0 → ℝ) :=
  projectiveLimit gaussianProjectiveFamily isProjectiveMeasureFamily_gaussianProjectiveFamily

instance IsProbabilityMeasure_gaussianLimit :
    IsProbabilityMeasure gaussianLimit :=
  isProbabilityMeasure_projectiveLimit isProjectiveMeasureFamily_gaussianProjectiveFamily

lemma isProjectiveLimit_gaussianLimit :
    IsProjectiveLimit gaussianLimit gaussianProjectiveFamily :=
  isProjectiveLimit_projectiveLimit isProjectiveMeasureFamily_gaussianProjectiveFamily

lemma _root_.MeasureTheory.IsProjectiveLimit.hasLaw_restrict {ι : Type*} {X : ι → Type*}
    {mX : ∀ i, MeasurableSpace (X i)} {μ : Measure (Π i, X i)}
    {P : (I : Finset ι) → Measure (Π i : I, X i)} (h : IsProjectiveLimit μ P) {I : Finset ι} :
    HasLaw I.restrict (P I) μ where
  map_eq := h I

lemma hasLaw_restrict_gaussianLimit {I : Finset ℝ≥0} :
    HasLaw I.restrict (gaussianProjectiveFamily I) gaussianLimit :=
  isProjectiveLimit_gaussianLimit.hasLaw_restrict

lemma hasLaw_eval_gaussianLimit {t : ℝ≥0} :
    HasLaw (fun x ↦ x t) (gaussianReal 0 t) gaussianLimit :=
  hasLaw_eval_gaussianProjectiveFamily (⟨t, by simp⟩ : ({t} : Finset ℝ≥0)) |>.comp
    hasLaw_restrict_gaussianLimit

lemma covariance_eval_gaussianLimit {s t : ℝ≥0} :
    cov[fun x ↦ x s, fun x ↦ x t; gaussianLimit] = min s t := by
  convert (hasLaw_restrict_gaussianLimit (I := {s, t})).covariance_fun_comp
    (f := Function.eval ⟨s, by simp⟩) (g := Function.eval ⟨t, by simp⟩) ?_ ?_
  · rw [covariance_eval_gaussianProjectiveFamily]
  all_goals exact Measurable.aemeasurable (by fun_prop)

end ProbabilityTheory
