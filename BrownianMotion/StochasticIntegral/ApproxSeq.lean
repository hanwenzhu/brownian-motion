/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Architect
import BrownianMotion.StochasticIntegral.Cadlag
import BrownianMotion.StochasticIntegral.UniformIntegrable

/-! # Discrete approximation of a stopping time

-/

open Filter TopologicalSpace Function Bornology
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {ι Ω E : Type*} [TopologicalSpace ι] [LinearOrder ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → E} {τ σ : Ω → WithTop ι} {i : ι}

/-- Given a random time `τ`, a discrete approximation sequence `τn` of `τ` is a sequence of
stopping times with countable range that converges to `τ` from above almost surely. -/
@[ext, blueprint
  "def:approxSeq"
  (title := "Discrete approximation sequence")
  (statement := /-- Given a stopping time \(\tau : \Omega \to T \cup \{\infty\}\), a sequence of
    stopping times \((\tau_n)_{n \in \mathbb{N}}\) is called an
    discrete approximation of \(\tau\) if \(\tau_n(\Omega)\) is countable for each \(n\) and
    \(\tau_n \downarrow \tau\) a.s. as \(n \to \infty\). -/)]
structure DiscreteApproxSequence (𝓕 : Filtration ι mΩ) (τ : Ω → WithTop ι)
    (μ : Measure Ω := by volume_tac) where
  /-- The sequence of stopping times approximating `τ`. -/
  seq : ℕ → Ω → WithTop ι
  /-- Each `τn` is a stopping time. -/
  isStoppingTime : ∀ n, IsStoppingTime 𝓕 (seq n)
  /-- Each `τn` has countable range. -/
  countable : ∀ n, (Set.range (seq n)).Countable
  /-- The sequence is antitone. -/
  antitone : Antitone seq
  /-- Each `τn` is greater than or equal to `τ`. -/
  le : ∀ n, τ ≤ seq n
  /-- The sequence converges to `τ` almost surely. -/
  tendsto : ∀ᵐ ω ∂μ, Tendsto (seq · ω) atTop (𝓝 (τ ω))

instance : FunLike (DiscreteApproxSequence 𝓕 τ μ) ℕ (Ω → WithTop ι) where
  coe s := s.seq
  coe_injective' s t h := by
    cases s; cases t; congr

-- Should replace `isStoppingTime_const`
theorem isStoppingTime_const' {ι : Type*} [Preorder ι] (f : Filtration ι mΩ) (i : WithTop ι) :
    IsStoppingTime f fun _ => i := fun j => by simp only [MeasurableSet.const]

/-- A time index `ι` is said to be approximable if for any stopping time `τ` on `ι`, there exists
a discrete approximation sequence of `τ`. -/
@[blueprint
  "def:approximableTimeIndex"
  (title := "Approximable time index")
  (statement := /-- A time index set \(T\) is said to be approximable if for any stopping time
    \(\tau : \Omega \to T \cup \{\infty\}\), there exists a discrete approximation sequence
    \((\tau_n)\) of \(\tau\). -/)]
class Approximable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace ι] [LinearOrder ι]
    [OrderTopology ι] (𝓕 : Filtration ι mΩ) (μ : Measure Ω := by volume_tac) where
  /-- For any stopping time `τ`, there exists a discrete approximation sequence of `τ`. -/
  approxSeq :
    ∀ τ : Ω → WithTop ι, IsStoppingTime 𝓕 τ → DiscreteApproxSequence 𝓕 τ μ

/-- Given a stopping time `τ` on an approximable time index, we obtain an associated discrete
approximation sequence. -/
def IsStoppingTime.discreteApproxSequence
    (h : IsStoppingTime 𝓕 τ) (μ : Measure Ω) [Approximable 𝓕 μ] :
    DiscreteApproxSequence 𝓕 τ μ := Approximable.approxSeq τ h

@[blueprint
  "lem:stoppingTime_approximationNat"
  (statement := /-- $T = \mathbb{N}$ is an approximable time index. -/)
  (proof := /-- Immediate as we can take \(\tau_n = \tau\) for all \(n\). -/)
  (latexEnv := "lemma")]
instance _root_.Nat.approximable {𝓕 : Filtration ℕ mΩ} : Approximable 𝓕 μ := sorry

@[blueprint
  "lem:stoppingTime_approximation"
  (statement := /-- $T = \mathbb{R}_+$ is an approximable time index. In particular,
    for any stopping time $\tau$ on $\overline{\mathbb{R}_+}$, defining $\tau_n =  2^{-n} \lceil 2^n
    \tau \rceil$,
    we have that $(\tau_n)$ is a discrete approximation sequence of $\tau$. -/)
  (proof := /-- Clearly $\tau_n \downarrow \tau$ as $n \to \infty$ and so it remains to show that
    each $\tau_n$ is a stopping time.
    Indeed,
    \[\{\tau_n \le t\} = \{\tau \le 2^{-n} \lfloor 2^n t\rfloor\}
      \in \mathcal{F}_{2^{-n} \lfloor 2^n t\rfloor} \subseteq \mathcal{F}_t\]
    where the last inclusion follows as \(2^{-n} \lfloor 2^n t\rfloor \le t\). -/)
  (latexEnv := "lemma")]
instance _root_.NNReal.approximable {𝓕 : Filtration ℝ≥0 mΩ} : Approximable 𝓕 μ := sorry

/-- The constant discrete approximation sequence. -/
def discreteApproxSequence_const (𝓕 : Filtration ι mΩ) (i : WithTop ι) :
    DiscreteApproxSequence 𝓕 (Function.const _ i) μ where
  seq := fun _ ↦ fun _ ↦ i
  isStoppingTime := fun n ↦ isStoppingTime_const' 𝓕 i
  countable := fun n ↦ by
    by_cases h : Nonempty Ω
    · simp
    · rw [not_nonempty_iff] at h
      rw [Set.range_eq_empty]
      exact Set.countable_empty
  antitone := antitone_const
  le := fun n ω ↦ le_rfl
  tendsto := by simp

@[blueprint
  "lem:tendsto_stoppedValue_discreteApproxSequence"
  (statement := /-- Given a right continuous process \(X\) and a discrete approximation sequence
    \((\tau_n)\) of the stopping time \(\tau\), we have that
    \[\lim_{n \to \infty} X_{\tau_n} = X_\tau \text{ a.s.}\] -/)
  (proof := /-- This follows directly as \(X\) is right continuous and \(\tau_n \downarrow \tau\)
    a.s. -/)
  (latexEnv := "lemma")]
lemma tendsto_stoppedValue_discreteApproxSequence [Nonempty ι] [TopologicalSpace E]
    (τn : DiscreteApproxSequence 𝓕 τ μ) (hX : ∀ ω, RightContinuous (X · ω)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ stoppedValue X (τn.seq n) ω) atTop (𝓝 (stoppedValue X τ ω)) := by
  sorry

/-- For `τ` a time bounded by `i` and `τn` a discrete approximation sequence of `τ`,
`discreteApproxSequence_of` is the discrete approximation sequence of `τ` defined by `τn ∧ i`. -/
@[blueprint
  "lem:discreteApproxSequence_of"
  (statement := /-- Let \(\tau\) be a stopping time bounded by \(t \in T\) and \((\tau_n)\) be a
    discrete approximation sequence of \(\tau\).
    Then, the sequence of stopping times \(\tau_n \wedge t\) is also a discrete approximation
    sequence of \(\tau\). -/)
  (latexEnv := "lemma")]
def discreteApproxSequence_of {i : ι}
    (𝓕 : Filtration ι mΩ) (hτ : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) :
    DiscreteApproxSequence 𝓕 τ μ where
  seq := fun m ↦ min (τn m) (Function.const _ i)
  isStoppingTime := fun m ↦ (τn.isStoppingTime m).min (isStoppingTime_const _ _)
  countable := fun m ↦ by
    have : Set.range ((τn m) ⊓ (Function.const _ i))
      ⊆ Set.range (τn m) ∪ {(i : WithTop ι)} := fun _ ↦ by simp; grind
    · refine Set.Countable.mono (this) ?_
      rw [Set.union_singleton, Set.countable_insert]
      exact τn.countable m
  antitone := τn.antitone.inf antitone_const
  le := fun m ↦ le_inf (τn.le m) <| fun ω ↦ hτ ω
  tendsto := by
    filter_upwards [τn.tendsto] with ω hω
    convert hω.min (tendsto_const_nhds (x := (i : WithTop ι)))
    exact (min_eq_left (hτ ω)).symm

lemma discreteApproxSequence_of_le {i : ι}
    (hτ : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) (m : ℕ) (ω : Ω) :
    discreteApproxSequence_of 𝓕 hτ τn m ω ≤ i :=
  min_le_right _ _

/-- The minimum of two discrete approximation sequences is a discrete approximation sequence of the
minimum of the two stopping times. -/
def DiscreteApproxSequence.inf
    (τn : DiscreteApproxSequence 𝓕 τ μ) (σn : DiscreteApproxSequence 𝓕 σ μ) :
    DiscreteApproxSequence 𝓕 (τ ⊓ σ) μ where
  seq := fun m ↦ min (τn m) (σn m)
  isStoppingTime := fun m ↦ (τn.isStoppingTime m).min (σn.isStoppingTime m)
  countable := fun m ↦ by
    refine ((τn.countable m).union (σn.countable m)).mono <| fun i ↦ ?_
    simp only [Set.mem_range, Pi.inf_apply, Set.mem_union, forall_exists_index, min_eq_iff]
    rintro ω (⟨rfl, -⟩ | ⟨rfl, -⟩)
    · exact Or.inl ⟨ω, rfl⟩
    · exact Or.inr ⟨ω, rfl⟩
  antitone := τn.antitone.inf σn.antitone
  le := fun m ↦ inf_le_inf (τn.le m) (σn.le m)
  tendsto := by
    filter_upwards [τn.tendsto, σn.tendsto] with ω hωτ hωσ using hωτ.min hωσ

/-- The minimum of two discrete approximation sequence of the same stopping time. -/
def DiscreteApproxSequence.inf'
    (τn : DiscreteApproxSequence 𝓕 τ μ) (τn' : DiscreteApproxSequence 𝓕 τ μ) :
    DiscreteApproxSequence 𝓕 τ μ where
  seq := fun m ↦ min (τn m) (τn' m)
  isStoppingTime := fun m ↦ (τn.isStoppingTime m).min (τn'.isStoppingTime m)
  countable := fun m ↦ by
    refine ((τn.countable m).union (τn'.countable m)).mono <| fun i ↦ ?_
    simp only [Set.mem_range, Pi.inf_apply, Set.mem_union, forall_exists_index, min_eq_iff]
    rintro ω (⟨rfl, -⟩ | ⟨rfl, -⟩)
    · exact Or.inl ⟨ω, rfl⟩
    · exact Or.inr ⟨ω, rfl⟩
  antitone := τn.antitone.inf τn'.antitone
  le := fun m ↦ le_inf (τn.le m) (τn'.le m)
  tendsto := by
    filter_upwards [τn.tendsto, τn'.tendsto] with ω hωτ hωσ using min_self (a := τ ω) ▸ hωτ.min hωσ

@[simp] lemma DiscreteApproxSequence.inf'_eq
    (τn : DiscreteApproxSequence 𝓕 τ μ) (τn' : DiscreteApproxSequence 𝓕 τ μ) (n : ℕ) :
    τn.inf' τn' n = min (τn n) (τn' n) :=
  rfl

@[simp] lemma DiscreteApproxSequence.inf'_apply
    (τn : DiscreteApproxSequence 𝓕 τ μ) (τn' : DiscreteApproxSequence 𝓕 τ μ) (n : ℕ) (ω : Ω) :
    τn.inf' τn' n ω = min (τn n ω) (τn' n ω) :=
  rfl

instance : LE (DiscreteApproxSequence 𝓕 τ μ) :=
  ⟨fun τn σn ↦ ∀ n, τn n ≤ σn n⟩

instance : PartialOrder (DiscreteApproxSequence 𝓕 τ μ) where
  le_refl := fun τn n ↦ le_rfl
  le_trans := fun τn σn ρn h₁ h₂ n ↦ (h₁ n).trans (h₂ n)
  le_antisymm := fun τn σn h₁ h₂ ↦ by
    ext n ω; exact le_antisymm (h₁ n ω) (h₂ n ω)

instance : SemilatticeInf (DiscreteApproxSequence 𝓕 τ μ) where
  inf := DiscreteApproxSequence.inf'
  inf_le_left := fun a₁ a₂ n ω ↦ by simp
  inf_le_right := fun a₁ a₂ n ω ↦ by simp
  le_inf := fun a₁ a₂ a₃ h₁ h₂ n ω ↦ by aesop

lemma DiscreteApproxSequence.discreteApproxSequence_of_le_inf_le_of_left {i : ι}
    (τn : DiscreteApproxSequence 𝓕 τ μ) (σn : DiscreteApproxSequence 𝓕 σ μ)
    (hτ : ∀ ω, τ ω ≤ i) (m : ℕ) (ω : Ω) :
    (discreteApproxSequence_of 𝓕 hτ τn).inf σn m ω ≤ i :=
  (min_le_left _ _).trans <| discreteApproxSequence_of_le hτ τn m ω

variable [Nonempty ι] [OrderBot ι] [FirstCountableTopology ι] [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma uniformIntegrable_stoppedValue_discreteApproxSequence_of_le
    (h : Martingale X 𝓕 μ) (τn : DiscreteApproxSequence 𝓕 τ μ) (hτn_le : ∀ n ω, τn n ω ≤ i) :
    UniformIntegrable (fun m ↦ stoppedValue X (τn m)) 1 μ :=
  h.uniformIntegrable_stoppedValue_of_countable_range _
    (τn.isStoppingTime) (fun n ω ↦ hτn_le n ω) (τn.countable)

@[blueprint
  "lem:uniformIntegrable_stoppedValue_discreteApproxSequence"
  (statement := /-- Let \(\tau\) be a stopping time bounded by \(t \in T\) and \((\tau_n)\) be a
    discrete approximation sequence of \(\tau\).
    Then, for any martingale \(X\), the sequence of stopped values \((X_{\tau_n \wedge t})\) is
    uniformly integrable. -/)
  (proof := /-- Follows directly by
    Lemma~\ref{lem:uniformIntegrable_stoppedValue_martingale_of_countable_range} and
    Lemma~\ref{lem:discreteApproxSequence_of}. -/)
  (latexEnv := "lemma")]
lemma uniformIntegrable_stoppedValue_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) :
    UniformIntegrable (fun m ↦ stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m)) 1 μ :=
  uniformIntegrable_stoppedValue_discreteApproxSequence_of_le h _
    (discreteApproxSequence_of_le hτ_le τn)

lemma integrable_stoppedValue_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) (m : ℕ) :
    Integrable (stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m)) μ :=
  ((uniformIntegrable_stoppedValue_discreteApproxSequence h hτ_le τn).memLp m).integrable
    le_rfl

lemma aestronglyMeasurable_stoppedValue_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, RightContinuous (X · ω))
    (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) :
    AEStronglyMeasurable (stoppedValue X τ) μ :=
  aestronglyMeasurable_of_tendsto_ae _
    (fun m ↦ (integrable_stoppedValue_of_discreteApproxSequence h hτ_le τn m).1)
    (tendsto_stoppedValue_discreteApproxSequence (discreteApproxSequence_of 𝓕 hτ_le τn) hRC)

theorem stoppedValue_ae_eq_condExp_discreteApproxSequence_of
    (h : Martingale X 𝓕 μ) (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) (m : ℕ) :
    stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m)
    =ᵐ[μ] μ[X i|((discreteApproxSequence_of 𝓕 hτ_le τn).isStoppingTime m).measurableSpace] :=
  h.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      (DiscreteApproxSequence.isStoppingTime _ m)
      (fun ω ↦ discreteApproxSequence_of_le hτ_le τn m ω) (DiscreteApproxSequence.countable _ m)

attribute [blueprint
  "lem:vitali"
  (title := "Vitali convergence theorem")
  (statement := /-- A sequence of functions converges in $L^1$ if and only if it converges in
    probability and is uniformly integrable. -/)
  (latexEnv := "lemma")]
  MeasureTheory.tendstoInMeasure_iff_tendsto_Lp_finite

@[blueprint
  "lem:tendsto_eLpNorm_stoppedValue_discreteApproxSequence"
  (statement := /-- Let \(\tau\) be a stopping time bounded by \(t \in T\) and \((\tau_n)\) be a
    discrete approximation sequence of \(\tau\).
    Then, for any right continuous martingale \(X\), \(X_{\tau} \in L^1\) and \(X_{\tau_n \wedge t}
    \to X_{\tau}\) in \(L^1\) as \(n \to \infty\). -/)
  (proof := /-- By Lemma~\ref{lem:tendsto_stoppedValue_discreteApproxSequence}, as \(X\) is right
    continuous we have that \(X_{\tau_n \wedge t} \to X_{\tau}\) a.s. and so,
    also in probability. Moreover, by
    Lemma~\ref{lem:uniformIntegrable_stoppedValue_discreteApproxSequence}, the sequence \((X_{\tau_n
    \wedge t})\) is uniformly integrable.
    Thus, by Lemma~\ref{lem:memLp_of_tendstoInMeasure} and the Vitali convergence theorem
    (Lemma~\ref{lem:vitali}), it
    follows that \(X_{\tau} \in L^1\) and \(X_{\tau_n \wedge t} \to X_{\tau}\) in \(L^1\) as \(n \to
    \infty\). -/)
  (latexEnv := "lemma")]
lemma tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, RightContinuous (X · ω))
    (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) :
    Tendsto (fun i ↦
      eLpNorm (stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn i) - stoppedValue X τ) 1 μ)
      atTop (𝓝 0) :=
  tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun m ↦ (integrable_stoppedValue_of_discreteApproxSequence h hτ_le τn m).1)
    ((uniformIntegrable_stoppedValue_discreteApproxSequence h hτ_le
    τn).memLp_of_tendstoInMeasure 1 (tendstoInMeasure_of_tendsto_ae
      (fun m ↦ (integrable_stoppedValue_of_discreteApproxSequence h hτ_le τn m).1) <|
      tendsto_stoppedValue_discreteApproxSequence _ hRC))
    (uniformIntegrable_stoppedValue_discreteApproxSequence h hτ_le τn).2.1
    (tendstoInMeasure_of_tendsto_ae
      (fun m ↦ (integrable_stoppedValue_of_discreteApproxSequence h hτ_le τn m).1) <|
      tendsto_stoppedValue_discreteApproxSequence _ hRC)

lemma integrable_stoppedValue_of_discreteApproxSequence'
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, RightContinuous (X · ω))
    (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) :
    Integrable (stoppedValue X τ) μ :=
  let τn' := discreteApproxSequence_of 𝓕 hτ_le τn
  UniformIntegrable.integrable_of_tendstoInMeasure
    (h.uniformIntegrable_stoppedValue_of_countable_range τn' τn'.isStoppingTime
      (discreteApproxSequence_of_le hτ_le τn) τn'.countable)
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun m ↦ (integrable_stoppedValue_of_discreteApproxSequence h hτ_le τn m).1)
      (aestronglyMeasurable_stoppedValue_of_discreteApproxSequence h hRC hτ_le τn') <|
      tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence h hRC hτ_le τn)

lemma tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence_of_le
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, RightContinuous (X · ω))
    (τn : DiscreteApproxSequence 𝓕 τ μ) (hτn_le : ∀ n ω, τn n ω ≤ i) :
    Tendsto (fun i ↦ eLpNorm (stoppedValue X (τn i) - stoppedValue X τ) 1 μ) atTop (𝓝 0) := by
  have hτ_le : ∀ ω, τ ω ≤ i := fun ω ↦ (τn.le 0 ω).trans (hτn_le 0 ω)
  refine tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun m ↦ (((uniformIntegrable_stoppedValue_discreteApproxSequence_of_le
      h τn hτn_le).memLp m).integrable le_rfl).1) ?_
    (h.uniformIntegrable_stoppedValue_of_countable_range τn τn.isStoppingTime
      hτn_le τn.countable).2.1
    (tendstoInMeasure_of_tendsto_ae
      (fun m ↦ (((uniformIntegrable_stoppedValue_discreteApproxSequence_of_le
      h τn hτn_le).memLp m).integrable le_rfl).1) <|
      tendsto_stoppedValue_discreteApproxSequence _ hRC)
  rw [memLp_one_iff_integrable]
  exact integrable_stoppedValue_of_discreteApproxSequence' h hRC hτ_le τn

end MeasureTheory
