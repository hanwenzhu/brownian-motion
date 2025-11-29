/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
import Architect
import Mathlib.Probability.Process.Stopping
import BrownianMotion.StochasticIntegral.Predictable
import BrownianMotion.Auxiliary.WithTop
import BrownianMotion.Auxiliary.IsStoppingTime
import BrownianMotion.Auxiliary.StoppedProcess
import BrownianMotion.StochasticIntegral.Cadlag

/-! # Local properties of processes

-/

open MeasureTheory Filter Filtration
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A localizing sequence is a sequence of stopping times that tends almost surely to infinity. -/
@[blueprint
  "def:preLocalizingSequence"
  (statement := /-- A pre-localizing sequence is a sequence of stopping times $(\tau_n)_{n \in
    \mathbb{N}}$ such that $\tau_n \to \infty$ as $n \to \infty$ (a.s.). -/)]
structure IsPreLocalizingSequence [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → WithTop ι) (P : Measure Ω := by volume_tac) :
    Prop where
  isStoppingTime : ∀ n, IsStoppingTime 𝓕 (τ n)
  tendsto_top : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤)

/-- A localizing sequence is a sequence of stopping times that is almost surely increasing and
tends almost surely to infinity. -/
@[blueprint
  "def:localizingSequence"
  (title := "Localizing sequence")
  (statement := /-- A localizing sequence is a sequence of stopping times $(\tau_n)_{n \in
    \mathbb{N}}$ such that $\tau_n$ is non-decreasing and $\tau_n \to \infty$ as $n \to \infty$
    (a.s.).
    That is, it is a pre-localizing sequence that is also almost surely non-decreasing. -/)]
structure IsLocalizingSequence [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → WithTop ι)
    (P : Measure Ω := by volume_tac) extends IsPreLocalizingSequence 𝓕 τ P where
  mono : ∀ᵐ ω ∂P, Monotone (τ · ω)

@[blueprint
  "lem:localizingSequence_const_top"
  (statement := /-- The constant sequence $\tau_n = \infty$ is a localizing sequence. -/)
  (latexEnv := "lemma")]
lemma isLocalizingSequence_const_top [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) : IsLocalizingSequence 𝓕 (fun _ _ ↦ ⊤) P where
  isStoppingTime n := by simp [IsStoppingTime]
  mono := ae_of_all _ fun _ _ _ _ ↦ by simp
  tendsto_top := by filter_upwards [] with ω using tendsto_const_nhds

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

@[blueprint
  "lem:localizingSequence_min"
  (statement := /-- Let $(\sigma_n), (\tau_n)$ be localizing sequences.
    Then $(\sigma_n \wedge \tau_n)$ is a localizing sequence. -/)
  (latexEnv := "lemma")]
lemma IsLocalizingSequence.min [TopologicalSpace ι] [OrderTopology ι] {τ σ : ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : IsLocalizingSequence 𝓕 σ P) :
    IsLocalizingSequence 𝓕 (min τ σ) P where
  isStoppingTime n := (hτ.isStoppingTime n).min (hσ.isStoppingTime n)
  mono := by filter_upwards [hτ.mono, hσ.mono] with ω hτω hσω; exact hτω.min hσω
  tendsto_top := by
    filter_upwards [hτ.tendsto_top, hσ.tendsto_top] with ω hτω hσω using hτω.min hσω

variable [OrderBot ι]

@[simp]
lemma stoppedProcess_const_top : stoppedProcess X (fun _ ↦ ⊤) = X := by
  unfold stoppedProcess
  simp

attribute [blueprint
  "def:stoppedProcess"
  (title := "Stopped process")
  (statement := /-- Let $X : T \to \Omega \to E$ be a stochastic process and let $\tau : \Omega \to
    T$.
    The stopped process with respect to $\tau$ is defined by
    \begin{align*}
      (X^{\tau})_t = \begin{cases}
        X_t & \text{if } t \le \tau \\
        X_{\tau} & \text{otherwise}
      \end{cases}
    \end{align*} -/)]
  MeasureTheory.stoppedProcess

/-- A stochastic process `X` is said to satisfy a property `p` locally with respect to a
filtration `𝓕` if there exists a localizing sequence `(τ_n)` such that for all `n`, the stopped
process of `fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)` satisfies `p`. -/
@[blueprint
  "def:locally"
  (title := "Local property")
  (statement := /-- Let $P$ be a class of stochastic processes (or equivalently a predicate on
    stochastic processes).
    We say that a stochastic process $X : T \to \Omega \to E$ is locally in $P$ (or satisfies $P$
    locally) if there exists a localizing sequence $(\tau_n)_{n \in \mathbb{N}}$ such that for all
    $n \in \mathbb{N}$, the process $X^{\tau_n}\mathbb{I}_{\tau_n > 0}$ is in $P$ (in which
    $X^{\tau_n}$ denotes the stopped process).
    We denote the class of processes that are locally in $P$ by $P_{\mathrm{loc}}$. -/)]
def Locally [TopologicalSpace ι] [OrderTopology ι] [Zero E]
    (p : (ι → Ω → E) → Prop) (𝓕 : Filtration ι mΩ)
    (X : ι → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∃ τ : ℕ → Ω → WithTop ι, IsLocalizingSequence 𝓕 τ P ∧
    ∀ n, p (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))

section Locally

variable [TopologicalSpace ι] [OrderTopology ι]

/-- A localizing sequence, witness of the local property of the stochastic process. -/
@[blueprint
  "def:locally"
  (title := "Local property")
  (statement := /-- Let $P$ be a class of stochastic processes (or equivalently a predicate on
    stochastic processes).
    We say that a stochastic process $X : T \to \Omega \to E$ is locally in $P$ (or satisfies $P$
    locally) if there exists a localizing sequence $(\tau_n)_{n \in \mathbb{N}}$ such that for all
    $n \in \mathbb{N}$, the process $X^{\tau_n}\mathbb{I}_{\tau_n > 0}$ is in $P$ (in which
    $X^{\tau_n}$ denotes the stopped process).
    We denote the class of processes that are locally in $P$ by $P_{\mathrm{loc}}$. -/)]
noncomputable
def Locally.localSeq [Zero E] (hX : Locally p 𝓕 X P) :
    ℕ → Ω → WithTop ι :=
  hX.choose

lemma Locally.IsLocalizingSequence [Zero E] (hX : Locally p 𝓕 X P) :
    IsLocalizingSequence 𝓕 (hX.localSeq) P :=
  hX.choose_spec.1

lemma Locally.stoppedProcess [Zero E] (hX : Locally p 𝓕 X P) (n : ℕ) :
    p (stoppedProcess (fun i ↦ {ω | ⊥ < hX.localSeq n ω}.indicator (X i)) (hX.localSeq n)) :=
  hX.choose_spec.2 n

@[blueprint
  "lem:implies_locally"
  (statement := /-- For any class of processes $P$, we have $P \subseteq P_{\mathrm{loc}}$. -/)
  (proof := /-- Take $\tau_n = \infty$ for all $n$. -/)
  (latexEnv := "lemma")]
lemma locally_of_prop [Zero E] (hp : p X) : Locally p 𝓕 X P :=
  ⟨fun n _ ↦ (⊤ : WithTop ι), isLocalizingSequence_const_top _ _, by simpa⟩

@[blueprint
  "lem:locally_mono"
  (statement := /-- If $P \subseteq Q$ then $P_{\mathrm{loc}} \subseteq Q_{\mathrm{loc}}$. -/)
  (proof := /-- Let $X \in P_{\mathrm{loc}}$.
    Then there exists a localizing sequence $(\tau_n)_{n \in \mathbb{N}}$ such that for all $n \in
    \mathbb{N}$, $X^{\tau_n}\mathbb{I}_{\tau_n > 0} \in P$.
    Since $P \subseteq Q$, for all $n \in \mathbb{N}$, $X^{\tau_n}\mathbb{I}_{\tau_n > 0} \in Q$.
    Thus $X \in Q_{\mathrm{loc}}$. -/)
  (latexEnv := "lemma")]
lemma Locally.mono [Zero E] (hpq : ∀ X, p X → q X) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  ⟨hpX.localSeq, hpX.IsLocalizingSequence, fun n ↦ hpq _ <| hpX.stoppedProcess n⟩

lemma Locally.of_and [Zero E] (hX : Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P) :
    Locally p 𝓕 X P ∧ Locally q 𝓕 X P :=
  ⟨hX.mono <| fun _ ↦ And.left, hX.mono <| fun _ ↦ And.right⟩

lemma Locally.of_and_left [Zero E] (hX : Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P) :
    Locally p 𝓕 X P :=
  hX.of_and.left

lemma Locally.of_and_right [Zero E] (hX : Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P) :
    Locally q 𝓕 X P :=
  hX.of_and.right

end Locally

variable [Zero E]

/-- A property of stochastic processes is said to be stable if it is preserved under taking
the stopped process by a stopping time. -/
@[blueprint
  "def:stable"
  (statement := /-- A class of stochastic processes $P$ is stable if whenever $X$ is in $P$, then
    for any stopping time $\tau$, the process $X^{\tau}\mathbb{I}_{\tau > 0}$ is also in $P$. -/)]
def IsStable
    (𝓕 : Filtration ι mΩ) (p : (ι → Ω → E) → Prop) : Prop :=
    ∀ X : ι → Ω → E, p X → ∀ τ : Ω → WithTop ι, IsStoppingTime 𝓕 τ →
      p (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ)

lemma IsStable.and (p q : (ι → Ω → E) → Prop)
    (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q) :
    IsStable 𝓕 (fun X ↦ p X ∧ q X) :=
  fun _ hX τ hτ ↦ ⟨hp _ hX.left τ hτ, hq _ hX.right τ hτ⟩

variable [TopologicalSpace ι] [OrderTopology ι]

@[blueprint
  "lem:isStable_locally"
  (statement := /-- If $P$ is a stable class of processes, then $P_{\mathrm{loc}}$ is also stable.
    -/)
  (latexEnv := "lemma")]
lemma IsStable.isStable_locally (hp : IsStable 𝓕 p) :
    IsStable 𝓕 (fun Y ↦ Locally p 𝓕 Y P) := by
  intro X hX τ hτ
  refine ⟨hX.localSeq, hX.IsLocalizingSequence, fun n ↦ ?_⟩
  simp_rw [← stoppedProcess_indicator_comm', Set.indicator_indicator, Set.inter_comm,
    ← Set.indicator_indicator, stoppedProcess_stoppedProcess, inf_comm]
  rw [stoppedProcess_indicator_comm', ← stoppedProcess_stoppedProcess]
  exact hp _ (hX.stoppedProcess n) τ hτ

@[blueprint
  "lem:locally_inter"
  (statement := /-- If $P, Q$ are stable classes of processes then $(P\cap Q)_{\mathrm{loc}} =
    P_{\mathrm{loc}}\cap Q_{\mathrm{loc}}$. -/)
  (proof := /-- The forward direction is trivial so we only provide proof for the reverse.
    
    Suppose that $X \in P_{\mathrm{loc}}\cap Q_{\mathrm{loc}}$. Then, there exists localizing
    sequences $(\tau_n)_{n \in \mathbb{N}}$ and $(\sigma_n)_{n \in \mathbb{N}}$ such that
    $X^{\tau_n} \mathbb{I}_{\tau_n > 0}\in P$ and $X^{\sigma_n} \mathbb{I}_{\sigma_n > 0} \in Q$.
    Consequently, by the stability of $P$,
    \[X^{\sigma_n \wedge \tau_n} \mathbb{I}_{\sigma_n \wedge \tau_n > 0} = (X^{\tau_n}
    \mathbb{I}_{\tau_n > 0})^{\sigma_n \wedge \tau_n} \mathbb{I}_{\sigma_n \wedge \tau_n > 0} \in
    P.\]
    Similarly, by the stability of $Q$, $X^{\sigma_n \wedge \tau_n} \mathbb{I}_{\sigma_n \wedge
    \tau_n > 0} \in Q$. Thus, as $\sigma_n \wedge \tau_n$ is a localizing sequence by
    Lemma~\ref{lem:localizingSequence_min} and $X^{\sigma_n \wedge \tau_n} \mathbb{I}_{\sigma_n
    \wedge \tau_n > 0} \in P \cap Q$ for all $n$, it follows that $X \in (P \cap Q)_{\mathrm{loc}}$
    -/)
  (latexEnv := "lemma")]
lemma locally_and (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q) :
    Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P ↔ Locally p 𝓕 X P ∧ Locally q 𝓕 X P := by
  refine ⟨Locally.of_and, fun ⟨hpX, hqX⟩ ↦
    ⟨_, hpX.IsLocalizingSequence.min hqX.IsLocalizingSequence, fun n ↦ ⟨?_, ?_⟩⟩⟩
  · convert hp _ (hpX.stoppedProcess n) _ <| hqX.IsLocalizingSequence.isStoppingTime n using 1
    ext i ω
    rw [stoppedProcess_indicator_comm]
    simp_rw [Pi.inf_apply, lt_inf_iff, inf_comm (hpX.localSeq n)]
    rw [← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_comm,
      (_ : {ω | ⊥ < hpX.localSeq n ω ∧ ⊥ < hqX.localSeq n ω}
        = {ω | ⊥ < hpX.localSeq n ω} ∩ {ω | ⊥ < hqX.localSeq n ω}), Set.inter_comm]
    · simp_rw [← Set.indicator_indicator]
      rfl
    · rfl
  · convert hq _ (hqX.stoppedProcess n) _ <| hpX.IsLocalizingSequence.isStoppingTime n using 1
    ext i ω
    rw [stoppedProcess_indicator_comm]
    simp_rw [Pi.inf_apply, lt_inf_iff]
    rw [← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_comm,
      (_ : {ω | ⊥ < hpX.localSeq n ω ∧ ⊥ < hqX.localSeq n ω}
        = {ω | ⊥ < hpX.localSeq n ω} ∩ {ω | ⊥ < hqX.localSeq n ω})]
    · simp_rw [← Set.indicator_indicator]
      rfl
    · rfl

end LinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

lemma measure_iInter_of_ae_antitone {ι : Type*}
    [Countable ι] [Preorder ι] [IsDirected ι fun (x1 x2 : ι) ↦ x1 ≤ x2]
    {s : ι → Set Ω} (hs : ∀ᵐ ω ∂P, Antitone (s · ω))
    (hsm : ∀ (i : ι), MeasureTheory.NullMeasurableSet (s i) P) (hfin : ∃ (i : ι), P (s i) ≠ ⊤) :
    P (⋂ (i : ι), s i) = ⨅ (i : ι), P (s i) := by
  set t : ι → Set Ω := fun i ↦ ⋂ j ≤ i, s j with ht
  have hst (i : ι) : s i =ᵐ[P] t i := by
    filter_upwards [hs] with ω hω
    suffices ω ∈ s i ↔ ω ∈ t i by
      exact propext this
    simp only [ht, Set.mem_iInter]
    refine ⟨fun (h : s i ω) j hj ↦ ?_, fun h ↦ h i le_rfl⟩
    change s j ω
    specialize hω hj
    simp only [le_Prop_eq] at hω
    exact hω h
  rw [measure_congr <| EventuallyEq.countable_iInter hst, Antitone.measure_iInter]
  · exact iInf_congr <| fun i ↦ measure_congr <| (hst i).symm
  · intros i j hij
    simp only [ht]
    rw [(_ : ⋂ k ≤ j, s k = (⋂ k ≤ i, s k) ∩ (⋂ k ∈ {k | k ≤ j ∧ ¬ k ≤ i}, s k))]
    · exact Set.inter_subset_left
    · ext ω
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_inter_iff, and_imp]
      grind
  · exact fun _ ↦ NullMeasurableSet.iInter <| fun j ↦ NullMeasurableSet.iInter <| fun _ ↦ hsm j
  · obtain ⟨i, hi⟩ := hfin
    refine ⟨i, (lt_of_le_of_lt ?_ <| lt_top_iff_ne_top.2 hi).ne⟩
    rw [measure_congr (hst i)]

@[blueprint
  "lem:isLocalizingSequence_of_isPreLocalizingSequence"
  (statement := /-- If $(\tau_n)_{n \in \mathbb{N}}$ is a pre-localizing sequence, then the sequence
    defined by $\tau'_n = \inf_{m \ge n} \tau_m$ is a localizing sequence. -/)
  (latexEnv := "lemma")]
lemma isLocalizingSequence_of_isPreLocalizingSequence
    {τ : ℕ → Ω → WithTop ι} (h𝓕 : IsRightContinuous 𝓕) (hτ : IsPreLocalizingSequence 𝓕 τ P) :
    IsLocalizingSequence 𝓕 (fun i ω ↦ ⨅ j ≥ i, τ j ω) P where
  isStoppingTime (n : ℕ) := IsStoppingTime.iInf {j | j ≥ n} h𝓕 (fun j ↦ hτ.isStoppingTime j)
  mono :=  ae_of_all _ <| fun ω n m hnm ↦ iInf_le_iInf_of_subset <| fun k hk ↦ hnm.trans hk
  tendsto_top := by
    filter_upwards [hτ.tendsto_top] with ω hω
    replace hω := hω.liminf_eq
    rw [liminf_eq_iSup_iInf_of_nat] at hω
    rw [← hω]
    refine tendsto_atTop_iSup ?_
    intro n m hnm
    simp only [ge_iff_le, le_iInf_iff, iInf_le_iff]
    intro k hk i hi
    grind

/-- A stable property holds locally `p` for `X` if there exists a pre-localizing sequence `τ` for
which the stopped process of `fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)` satisfies `p`. -/
@[blueprint
  "lem:locally_of_isPreLocalizingSequence"
  (statement := /-- Let $P$ be a stable class of processes and let $(\tau_n)_{n \in \mathbb{N}}$ be
    a pre-localizing sequence such that for all $n \in \mathbb{N}$, $X^{\tau_n}\mathbb{I}_{\tau_n >
    0}$ is in $P$.
    If the filtration is right-continuous, then $X$ is locally in $P$. -/)
  (proof := /-- Using the localizing sequence defined by
    Lemma~\ref{lem:isLocalizingSequence_of_isPreLocalizingSequence} suffices. -/)
  (latexEnv := "lemma")]
lemma locally_of_isPreLocalizingSequence [Zero E] {τ : ℕ → Ω → WithTop ι}
    (hp : IsStable 𝓕 p) (h𝓕 : IsRightContinuous 𝓕) (hτ : IsPreLocalizingSequence 𝓕 τ P)
    (hpτ : ∀ n, p (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))) :
    Locally p 𝓕 X P := by
  refine ⟨_, isLocalizingSequence_of_isPreLocalizingSequence h𝓕 hτ, fun n ↦ ?_⟩
  have := hp _ (hpτ n) (fun ω ↦ ⨅ j ≥ n, τ j ω) <|
    (isLocalizingSequence_of_isPreLocalizingSequence h𝓕 hτ).isStoppingTime n
  rw [stoppedProcess_indicator_comm', ← stoppedProcess_stoppedProcess_of_le_right
    (τ := fun ω ↦ τ n ω) (fun _ ↦ (iInf_le _ n).trans <| iInf_le _ le_rfl),
    ← stoppedProcess_indicator_comm']
  convert this using 2
  ext i ω
  rw [stoppedProcess_indicator_comm', Set.indicator_indicator]
  congr 1
  ext ω'
  simp only [ge_iff_le, Set.mem_setOf_eq, Set.mem_inter_iff]
  exact ⟨fun h ↦ ⟨h, lt_of_lt_of_le h <| (iInf_le _ n).trans (iInf_le _ le_rfl)⟩, fun h ↦ h.1⟩

section

omit [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
variable [SecondCountableTopology ι] [IsFiniteMeasure P]

lemma isPreLocalizingSequence_of_isLocalizingSequence_aux'
    {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ T : ℕ → ι, Tendsto T atTop atTop
      ∧ ∀ n, ∃ k, P {ω | σ n k ω < min (τ n ω) (T n)} ≤ (1 / 2) ^ n := by
  obtain ⟨T, -, hT⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop ι
  refine ⟨T, hT, fun n ↦ ?_⟩
  by_contra hn; push_neg at hn
  suffices (1 / 2) ^ n ≤ P (⋂ k : ℕ, {ω | σ n k ω < min (τ n ω) (T n)}) by
    refine (by simp : ¬ (1 / 2 : ℝ≥0∞) ^ n ≤ 0) <| this.trans <| nonpos_iff_eq_zero.2 ?_
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [(hσ n).tendsto_top] with ω hTop hmem
    rw [WithTop.tendsto_atTop_nhds_top_iff] at hTop
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hmem
    obtain ⟨N, hN⟩ := hTop (T n)
    specialize hN N le_rfl
    specialize hmem N
    grind
  rw [measure_iInter_of_ae_antitone, le_iInf_iff]
  · exact fun k ↦ (hn k).le
  · filter_upwards [(hσ n).mono] with ω hω
    intros i j hij
    specialize hω hij
    simp only [lt_inf_iff, le_Prop_eq] at *
    change σ n j ω < τ n ω ∧ σ n j ω < T n → σ n i ω < τ n ω ∧ σ n i ω < T n
    grind
  · intro i
    refine MeasurableSet.nullMeasurableSet ?_
    have hMσ := ((hσ n).isStoppingTime i).measurable
    have hMτ := (hτ.isStoppingTime n).measurable
    simp_rw [lt_inf_iff]
    rw [(_ : {ω | σ n i ω < τ n ω ∧ σ n i ω < T n} = {ω | σ n i ω < τ n ω} ∩ {ω | σ n i ω < T n})]
    · exact MeasurableSet.inter
        (measurableSet_lt ((hσ n).isStoppingTime i).measurable' (hτ.isStoppingTime n).measurable')
        <| measurableSet_lt ((hσ n).isStoppingTime i).measurable' measurable_const
    · rfl
  · exact ⟨0, measure_ne_top P _⟩

/-- Auxliary defintion for `isPreLocalizingSequence_of_isLocalizingSequence` which constructs a
strictly increasing sequence from a given sequence. -/
def mkStrictMonoAux (x : ℕ → ℕ) : ℕ → ℕ
| 0 => x 0
| n + 1 => max (x (n + 1)) (mkStrictMonoAux x n) + 1

lemma mkStrictMonoAux_strictMono (x : ℕ → ℕ) : StrictMono (mkStrictMonoAux x) := by
  refine strictMono_nat_of_lt_succ <| fun n ↦ ?_
  simp only [mkStrictMonoAux]
  exact lt_of_le_of_lt (le_max_right (x (n + 1)) _) (lt_add_one (max (x (n + 1)) _))

lemma le_mkStrictMonoAux (x : ℕ → ℕ) : ∀ n, x n ≤ mkStrictMonoAux x n
| 0 => by simp [mkStrictMonoAux]
| n + 1 => by
    simp only [mkStrictMonoAux]
    exact (le_max_left (x (n + 1)) (mkStrictMonoAux x n)).trans <|
       Nat.le_add_right (max (x (n + 1)) (mkStrictMonoAux x n)) 1

lemma isPreLocalizingSequence_of_isLocalizingSequence_aux
    {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, StrictMono nk ∧ ∃ T : ℕ → ι, Tendsto T atTop atTop
      ∧ ∀ n, P {ω | σ n (nk n) ω < min (τ n ω) (T n)} ≤ (1 / 2) ^ n := by
  obtain ⟨T, hT, h⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux' hτ hσ
  choose nk hnk using h
  refine ⟨mkStrictMonoAux nk, mkStrictMonoAux_strictMono nk, T, hT, fun n ↦
    le_trans (EventuallyLE.measure_le ?_) (hnk n)⟩
  filter_upwards [(hσ n).mono] with ω hω
  specialize hω (le_mkStrictMonoAux nk n)
  simp only [lt_inf_iff, le_Prop_eq]
  change σ n (mkStrictMonoAux nk n) ω < τ n ω ∧ σ n (mkStrictMonoAux nk n) ω < T n →
    σ n (nk n) ω < τ n ω ∧ σ n (nk n) ω < T n
  grind

@[blueprint
  "lem:isPreLocalizingSequence_of_isLocalizingSequence"
  (statement := /-- Let $(\tau_n)_{n \in \mathbb{N}}$ be a localizing sequence and let
    $(\sigma_{n,k})_{k \in \mathbb{N}}$ be a localizing sequence for each $n$.
    Then, there exists a strictly increasing sequence $(k_n)_{n \in \mathbb{N}}$ such that the
    sequence defined by $\tau'_n = \tau_n \wedge \sigma_{n,k_n}$ is a pre-localizing sequence. -/)
  (proof := /-- For each $n$, since $\sigma_{n,k} \to \infty$ a.s. as $k \to \infty$, we may choose
    $k_n \in \mathbb{N}$ such that $P(\sigma_{n,k_n} < \tau_n \wedge n) \le 2^{-n}$.
    Then, defining $\tau'_n = \tau_n \wedge \sigma_{n,k_n}$, we have $\tau_n' \to \infty$ by the
    Borel-Cantelli lemma. -/)
  (latexEnv := "lemma")]
lemma isPreLocalizingSequence_of_isLocalizingSequence
    [NoMaxOrder ι] {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, StrictMono nk
      ∧ IsPreLocalizingSequence 𝓕 (fun i ω ↦ (τ i ω) ⊓ (σ i (nk i) ω)) P := by
  obtain ⟨nk, hnk, T, hT, hP⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux hτ hσ
  refine ⟨nk, hnk, fun n ↦ (hτ.isStoppingTime n).min ((hσ _).isStoppingTime _), ?_⟩
  have : ∑' n, P {ω | σ n (nk n) ω < min (τ n ω) (T n)} < ∞ :=
    lt_of_le_of_lt (ENNReal.summable.tsum_mono ENNReal.summable hP)
      (tsum_geometric_lt_top.2 <| by norm_num)
  have hτTop := hτ.tendsto_top
  filter_upwards [ae_eventually_notMem this.ne, hτTop] with ω hω hωτ
  replace hT := hωτ.min hT.tendsto_withTop_atTop_nhds_top
  simp_rw [eventually_atTop, not_lt, ← eventually_atTop] at hω
  rw [min_self] at hT
  rw [← min_self ⊤]
  refine hωτ.min <| tendsto_of_tendsto_of_tendsto_of_le_of_le' hT tendsto_const_nhds hω ?_
  simp only [le_top, eventually_atTop, ge_iff_le, implies_true, exists_const]

variable [DenselyOrdered ι] [NoMaxOrder ι] [Zero E]

/-- A stable property holding locally is idempotent. -/
@[blueprint
  "lem:locally_locally"
  (statement := /-- Suppose that the filtration is right-continuous.
    For any stable class of processes $P$, we have $(P_{\mathrm{loc}})_{\mathrm{loc}} =
    P_{\mathrm{loc}}$. -/)
  (proof := /-- $(P_{\mathrm{loc}})_{\mathrm{loc}} \supseteq P_{\mathrm{loc}}$ by
    Lemma~\ref{lem:isStable_locally} so we only prove the reverse inclusion.
    
    Let $X$ be a process in $(P_{\mathrm{loc}})_{\mathrm{loc}}$.
    By definition there exists a localizing sequence $(\tau_n)_{n \in \mathbb{N}}$ such that for all
    $n \in \mathbb{N}$, $X^{\tau_n}\mathbb{I}_{\tau_n > 0}$ is in $P_{\mathrm{loc}}$.
    By definition of $P_{\mathrm{loc}}$, for each $n$ there exists a localizing sequence
    $(\sigma_{n,k})_{k \in \mathbb{N}}$ such that for all $k \in \mathbb{N}$,
    $(X^{\tau_n}\mathbb{I}_{\tau_n > 0})^{\sigma_{n,k}}\mathbb{I}_{\sigma_{n,k} > 0}$ is in $P$.
    
    By Lemma~\ref{lem:locally_of_isPreLocalizingSequence}, it suffices to show that there exists a
    pre-localizing sequence $(\tau'_n)_{n \in \mathbb{N}}$ such that for all $n \in \mathbb{N}$,
    $X^{\tau'_n}\mathbb{I}_{\tau'_n > 0}$ is in $P$.
    Thus, using the localizing sequences $\tau'_n = \tau_n \wedge \sigma_{n, k_n}$ defined by
    Lemma~\ref{lem:isPreLocalizingSequence_of_isLocalizingSequence},
    it remains to argue that by stability of $P$, $X^{\tau'_n}\mathbb{I}_{\tau'_n > 0}$ is in $P$
    for all $n$.
    Indeed, this follows as $X^{\tau'_n}\mathbb{I}_{\tau'_n > 0} = ((X^{\tau_n}\mathbb{I}_{\tau_n >
    0})^{\sigma_{n,k_n}}\mathbb{I}_{\sigma_{n,k_n} > 0})^{\tau'_n}\mathbb{I}_{\tau'_n > 0}$ where
    $(X^{\tau_n}\mathbb{I}_{\tau_n > 0})^{\sigma_{n,k_n}}\mathbb{I}_{\sigma_{n,k_n} > 0}$ is in $P$
    by construction and $P$ is stable. -/)
  (latexEnv := "lemma")]
lemma locally_locally
    (h𝓕 : IsRightContinuous 𝓕) (hp : IsStable 𝓕 p) :
    Locally (fun Y ↦ Locally p 𝓕 Y P) 𝓕 X P ↔ Locally p 𝓕 X P := by
  refine ⟨fun hL ↦ ?_, fun hL ↦ ?_⟩
  · have hLL := hL.stoppedProcess
    choose τ hτ₁ hτ₂ using hLL
    obtain ⟨nk, hnk, hpre⟩ := isPreLocalizingSequence_of_isLocalizingSequence
      hL.IsLocalizingSequence hτ₁
    refine locally_of_isPreLocalizingSequence hp h𝓕 hpre <| fun n ↦ ?_
    specialize hτ₂ n (nk n)
    convert hτ₂ using 1
    ext i ω
    rw [stoppedProcess_indicator_comm', stoppedProcess_indicator_comm',
      stoppedProcess_stoppedProcess, stoppedProcess_indicator_comm']
    simp only [lt_inf_iff, Set.indicator_indicator]
    congr 1
    · ext ω'; simp only [And.comm, Set.mem_setOf_eq, Set.mem_inter_iff]
    · simp_rw [inf_comm]
      rfl
  · exact ⟨hL.localSeq, hL.IsLocalizingSequence, fun n ↦ locally_of_prop <| hL.stoppedProcess n⟩

/-- If `p` implies `q` locally, then `p` locally implies `q` locally. -/
@[blueprint
  "lem:local_induction"
  (title := "Local implication from global implication")
  (statement := /-- Suppose that the filtration is right-continuous.
    Let $P, Q$ be two classes of stochastic processes such that $P \subseteq Q_{\mathrm{loc}}$ and
    $Q$ is stable.
    Let $X$ be a stochastic process that satisfies $P$ locally.
    Then $X$ satisfies $Q$ locally.
    In short, if $P$ implies $Q$ locally, then $P$ locally implies $Q$ locally. -/)
  (proof := /-- Since $X \in P_{\mathrm{loc}}$, then $X \in (Q_{\mathrm{loc}})_{\mathrm{loc}}$ by
    assumption and Lemma~\ref{lem:locally_mono}.
    By Lemma \ref{lem:locally_locally}, $(Q_{\mathrm{loc}})_{\mathrm{loc}} = Q_{\mathrm{loc}}$.
    Thus $X \in Q_{\mathrm{loc}}$. -/)
  (latexEnv := "lemma")]
lemma locally_induction (h𝓕 : IsRightContinuous 𝓕)
    (hpq : ∀ Y, p Y → Locally q 𝓕 Y P) (hq : IsStable 𝓕 q) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  (locally_locally h𝓕 hq).1 <| hpX.mono hpq

lemma locally_induction₂ {r : (ι → Ω → E) → Prop} (h𝓕 : IsRightContinuous 𝓕)
    (hrpq : ∀ Y, r Y → p Y → Locally q 𝓕 Y P)
    (hr : IsStable 𝓕 r) (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q)
    (hrX : Locally r 𝓕 X P) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  locally_induction (p := fun Y ↦ r Y ∧ p Y) h𝓕 (and_imp.2 <| hrpq ·) hq
    <| (locally_and hr hp).2 ⟨hrX, hpX⟩

end

end ConditionallyCompleteLinearOrderBot

section cadlag

section LinearOrder

variable [LinearOrder ι] [OrderBot ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p : (ι → Ω → E) → Prop}

open Classical in
/-- Given a property on paths which holds almost surely for a stochastic process, we construct a
localizing sequence by setting the stopping time to be ∞ whenever the property holds. -/
noncomputable
def LocalizingSequence_of_prop (X : ι → Ω → E) (p : (ι → E) → Prop) : ℕ → Ω → WithTop ι :=
  Function.const _ <| fun ω ↦ if p (X · ω) then ⊤ else ⊥

lemma isStoppingTime_ae_const (𝓕 : Filtration ι mΩ) (P : Measure Ω) [HasUsualConditions 𝓕 P]
    (τ : Ω → WithTop ι) (c : WithTop ι) (hτ : τ =ᵐ[P] Function.const _ c) :
    IsStoppingTime 𝓕 τ := by
  intros i
  suffices P {ω | τ ω ≤ i} = 0 ∨ P {ω | τ ω ≤ ↑i}ᶜ = 0 by
    obtain h | h := this
    · exact 𝓕.mono bot_le _ <| HasUsualConditions.IsComplete h
    · exact (𝓕.mono bot_le _ <| HasUsualConditions.IsComplete h).of_compl
  obtain hle | hgt := le_or_gt c i
  · refine Or.inr <| ae_iff.1 ?_
    filter_upwards [hτ] with ω rfl using hle
  · refine Or.inl ?_
    rw [← compl_compl {ω | τ ω ≤ i}]
    refine ae_iff.1 ?_
    filter_upwards [hτ] with ω hω
    simp [hω, hgt]

variable [TopologicalSpace ι] [OrderTopology ι]

@[blueprint
  "lem:isLocalizingSequence_ae"
  (statement := /-- Let $P$ be a predicate on paths and suppose $X$ is a stochastic process
    satisfying $P$ a.s. Then, defining
    $$\tau_n(\omega) =
    \begin{cases}
      \infty & \text{if } X(\omega) \text{ satisfies } P \\
      0 & \text{otherwise}
    \end{cases}
    $$
    for all $n \in \mathbb{N}$, the sequence $(\tau_n)_{n \in \mathbb{N}}$ is a localizing sequence.
    -/)
  (latexEnv := "lemma")]
lemma isLocalizingSequence_ae
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) [HasUsualConditions 𝓕 P]
    {p : (ι → E) → Prop} (hpX : ∀ᵐ ω ∂P, p (X · ω)) :
    IsLocalizingSequence 𝓕 (LocalizingSequence_of_prop X p) P where
  isStoppingTime n := by
    refine isStoppingTime_ae_const 𝓕 P _ ⊤ ?_
    filter_upwards [hpX] with ω hω
    rw [LocalizingSequence_of_prop, Function.const_apply, Function.const_apply, if_pos hω]
  mono := ae_of_all _ <| fun ω i j hij ↦ by simp [LocalizingSequence_of_prop]
  tendsto_top := by
    filter_upwards [hpX] with ω hω
    simp [LocalizingSequence_of_prop, if_pos hω]

variable [NormedAddCommGroup E] [HasUsualConditions 𝓕 P]

open Classical in
@[blueprint
  "lem:locally_of_ae"
  (statement := /-- If $P$ be a predicate on paths such that the constant path $0$ satisfies $P$ and
    $X$ is a stochastic process satisfying $P$ a.s. then, $X$ satisfies $P$ locally. -/)
  (proof := /-- Follows directly by using the localizing sequence defined in
    Lemma~\ref{lem:isLocalizingSequence_ae}. -/)
  (latexEnv := "lemma")]
lemma locally_of_ae {p : (ι → E) → Prop} (hpX : ∀ᵐ ω ∂P, p (X · ω)) (hp₀ : p (0 : ι → E)) :
    Locally (fun X ↦ ∀ ω, p (X · ω)) 𝓕 X P := by
  refine ⟨_, isLocalizingSequence_ae 𝓕 P hpX, fun _ ω ↦ ?_⟩
  by_cases hω : p (X · ω)
  · convert hω using 2
    rw [stoppedProcess_eq_of_le, Set.indicator_of_mem]
    · simp [LocalizingSequence_of_prop, if_pos hω]
    · simp [LocalizingSequence_of_prop, if_pos hω]
  · convert hp₀ using 2
    rw [stoppedProcess_eq_of_ge, Set.indicator_of_notMem]
    · rfl
    · simp [LocalizingSequence_of_prop, if_neg hω]
    · simp [LocalizingSequence_of_prop, if_neg hω]

section NormedSpace

variable [NormedSpace ℝ E] [CompleteSpace E]

@[blueprint
  "lem:locally_rightContinuous"
  (statement := /-- A stochastic process $X$ is locally right continuous if and only if it is right
    continuous almost surely. -/)
  (proof := /-- If $X$ is a.s. right continuous, then it is locally right continuous by
    Lemma~\ref{lem:locally_of_ae}.
    
    On the other hand, assuming $X$ is locally right continuous, there exists a localizing sequence
    $(\tau_n)_{n \in \mathbb{N}}$ such that for all $n \in \mathbb{N}$ and $\omega \in \Omega$,
    $(X^{\tau_n}\mathbb{I}_{\tau_n > 0})(\omega)$ is right continuous.
    Thus, for almost surely every $\omega$ and any $t \in T$ there exists $N \in \mathbb{N}$ such
    that $\tau_N(\omega) > t + 1$ (not that the ordering of a.s. and for all is important). Hence,
    as
    $X_s(\omega) = (X^{\tau_N}\mathbb{I}_{\tau_N > 0})_s(\omega)$ on a neighborhood of $t$, we have
    that $X(\omega)$ is right continuous at $t$.
    Consequently, as $t$ was arbitrary, $X$ is a.s. right continuous. -/)
  (proofUses := ["lem:locally_of_ae"])
  (latexEnv := "lemma")]
lemma Locally.rightContinuous
    (hX : Locally (fun X ↦ ∀ ω, Function.RightContinuous (X · ω)) 𝓕 X P) :
    ∀ᵐ ω ∂P, Function.RightContinuous (X · ω) := by
  sorry

lemma locally_rightContinuous_iff :
    Locally (fun X ↦ ∀ ω, Function.RightContinuous (X · ω)) 𝓕 X P
    ↔ ∀ᵐ ω ∂P, Function.RightContinuous (X · ω) :=
  ⟨fun h ↦ h.rightContinuous, fun h ↦ locally_of_ae h <| fun _ ↦ continuousWithinAt_const⟩

@[blueprint
  "lem:locally_leftLimit"
  (statement := /-- A stochastic process $X$ has left limits locally if and only if it has left
    limits almost surely. -/)
  (proof := /-- Same proof as in Lemma~\ref{lem:locally_rightContinuous}. -/)
  (proofUses := ["lem:locally_of_ae"])
  (latexEnv := "lemma")]
lemma Locally.left_limit
    (hX : Locally (fun X ↦ ∀ ω, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[<] x) (𝓝 l)) 𝓕 X P) :
    ∀ᵐ ω ∂P, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[<] x) (𝓝 l) := by
  sorry

lemma locally_left_limit_iff :
    Locally (fun X ↦ ∀ ω, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[<] x) (𝓝 l)) 𝓕 X P ↔
      ∀ᵐ ω ∂P, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[<] x) (𝓝 l) :=
  ⟨fun h ↦ h.left_limit, fun h ↦ locally_of_ae
    (p := fun f ↦ ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)) h <| fun _ ↦ ⟨0, tendsto_const_nhds⟩⟩

@[blueprint
  "lem:locally_isCadlag"
  (statement := /-- A stochastic process $X$ is locally cadlag if and only if it is cadlag almost
    surely. -/)
  (proof := /-- The forward direction follows from Lemmas~\ref{lem:locally_rightContinuous} and
    \ref{lem:locally_leftLimit}
    while the reverse direction follows from Lemma~\ref{lem:locally_of_ae}. -/)
  (latexEnv := "lemma")]
lemma Locally.isCadlag
    (hX : Locally (fun X ↦ ∀ ω, IsCadlag (X · ω)) 𝓕 X P) :
    ∀ᵐ ω ∂P, IsCadlag (X · ω) := by
  filter_upwards [(hX.mono <| fun X h ω ↦ (h ω).right_continuous).rightContinuous,
    (hX.mono <| fun X h ω ↦ (h ω).left_limit).left_limit] with _ hω₁ hω₂ using ⟨hω₁, hω₂⟩

lemma locally_isCadlag_iff :
    Locally (fun X ↦ ∀ ω, IsCadlag (X · ω)) 𝓕 X P ↔ ∀ᵐ ω ∂P, IsCadlag (X · ω) :=
  ⟨fun h ↦ h.isCadlag, fun h ↦ locally_of_ae h
    ⟨fun _ ↦ continuousWithinAt_const, fun _ ↦ ⟨0, tendsto_const_nhds⟩⟩⟩

end NormedSpace

@[blueprint
  "lem:isStable_rightContinuous"
  (statement := /-- The class of right continuous processes is stable. -/)
  (proof := /-- Trivial. -/)
  (latexEnv := "lemma")]
lemma isStable_rightContinuous :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ ∀ ω, Function.RightContinuous (X · ω)) := by
  intro X hX τ hτ ω a
  dsimp [stoppedProcess]
  by_cases h_stop : (a : WithTop ι) < τ ω
  · let S := {x : ι | ↑x < τ ω}
    have hS_open : IsOpen S := isOpen_Iio.preimage WithTop.continuous_coe
    have ne_bot : ⊥ < τ ω := by
      rw [bot_lt_iff_ne_bot]
      exact ne_bot_of_gt h_stop
    have hS_mem : S ∈ 𝓝[>] a := mem_nhdsWithin_of_mem_nhds (hS_open.mem_nhds h_stop)
    apply ContinuousWithinAt.congr_of_eventuallyEq (hX ω a)
    · filter_upwards [hS_mem] with x hx
      have h_xle : x < τ ω := by exact hx
      simp_all only [Set.mem_setOf_eq, Set.indicator_of_mem, S]
      rw [min_eq_left ]
      · simp only [WithTop.untopD_coe]
      exact Std.le_of_lt h_xle
    · rw [min_eq_left h_stop.le]
      simp only [WithTop.untopD_coe, Set.indicator_apply_eq_self, Set.mem_setOf_eq, not_lt,
        le_bot_iff]
      intro h_bot
      simp_all only [not_lt_bot]
  · apply continuousWithinAt_const.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Ioi] at hx
      have h_bound : τ ω ≤ ↑x := le_trans (not_lt.mp h_stop) (le_of_lt (WithTop.coe_lt_coe.mpr hx))
      simp_all only [not_lt, inf_of_le_right]
      rfl
    simp only [min_eq_right (not_lt.mp h_stop)]


@[blueprint
  "lem:isStable_left_limit"
  (statement := /-- The class of processes with left limits is stable. -/)
  (proof := /-- Trivial. -/)
  (latexEnv := "lemma")]
lemma isStable_left_limit :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ ∀ ω, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[<] x) (𝓝 l)) := by
  intro X hX τ hτ ω x
  dsimp [stoppedProcess]
  by_cases h_stop : (x : WithTop ι) < τ ω
  · obtain ⟨l, hl⟩ := hX ω x
    use l
    let S := {y : ι | ↑y < τ ω}
    have hS_open : IsOpen S := isOpen_Iio.preimage WithTop.continuous_coe
    have ne_bot : ⊥ < τ ω := by
      rw [bot_lt_iff_ne_bot]
      exact ne_bot_of_gt h_stop
    have hS_mem : S ∈ 𝓝[<] x := mem_nhdsWithin_of_mem_nhds (hS_open.mem_nhds h_stop)
    apply Filter.Tendsto.congr' _ hl
    filter_upwards [hS_mem] with y hy
    have h_ylt : y < τ ω := hy
    simp_all only [Set.mem_setOf_eq, Set.indicator_of_mem, S]
    rw [min_eq_left]
    · simp only [WithTop.untopD_coe]
    exact Std.le_of_lt h_ylt
  · by_cases h_eq : (x : WithTop ι) = τ ω
    · obtain ⟨l, hl⟩ := hX ω x
      use l
      apply Filter.Tendsto.congr' _ hl
      have h_mem : {y : ι | ↑y < τ ω} ∈ 𝓝[<] x := by
        have : {y : ι | ↑y < τ ω} = {y : ι | y < x} := by
          ext y
          simp only [Set.mem_setOf_eq]
          rw [← h_eq, WithTop.coe_lt_coe]
        rw [this]
        exact self_mem_nhdsWithin
      filter_upwards [h_mem] with y hy
      have ne_bot : ⊥ < τ ω := by
        exact bot_lt_of_lt hy
      rw [min_eq_left (Std.le_of_lt hy)]
      simp only [WithTop.untopD_coe]
      simp_all only [lt_self_iff_false, not_false_eq_true, Set.mem_setOf_eq, Set.indicator_of_mem]
    · have h_gt : τ ω < (x : WithTop ι) := lt_of_le_of_ne (not_lt.mp h_stop) (Ne.symm h_eq)
      by_cases ne_bot : ⊥ < τ ω
      · use Set.indicator {ω' | ⊥ < τ ω'} (fun ω' ↦ X ((τ ω').untopD ⊥) ω') ω
        apply tendsto_const_nhds.congr'
        obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp
            (WithTop.lt_top_iff_ne_top.mp <| lt_of_lt_of_le h_gt le_top)
        have h_t_lt_x : t < x := by
          rw [← ht] at h_gt
          exact WithTop.coe_lt_coe.mp h_gt
        have h_Ioi_mem : Set.Ioi t ∈ 𝓝[<] x :=
          mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds h_t_lt_x)
        filter_upwards [h_Ioi_mem] with y hy
        simp only [Set.mem_Ioi] at hy
        simp_all only [not_lt, Set.mem_setOf_eq, Set.indicator_of_mem]
        rw [← ht, min_eq_right <| WithTop.coe_mono hy.le]
        simp only [WithTop.untopD_coe]
      · use 0
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with y _
        simp [ne_bot]

@[blueprint
  "lem:isStable_isCadlag"
  (statement := /-- The class of cadlag processes is stable. -/)
  (proof := /-- Follows from Lemmas~\ref{lem:isStable_rightContinuous} and
    \ref{lem:isStable_left_limit}. -/)
  (latexEnv := "lemma")]
lemma isStable_isCadlag :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ ∀ ω, IsCadlag (X · ω)) :=
  fun X hX τ hτ ω ↦
    ⟨isStable_rightContinuous X (fun ω' ↦ (hX ω').right_continuous) τ hτ ω,
      isStable_left_limit X (fun ω' ↦ (hX ω').left_limit) τ hτ ω⟩

end LinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [SecondCountableTopology ι] [DenselyOrdered ι] [NoMaxOrder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [IsFiniteMeasure P]
  {𝓕 : Filtration ι mΩ} [HasUsualConditions 𝓕 P] {X : ι → Ω → E} {p : (ι → Ω → E) → Prop}

lemma locally_isCadlag_iff_locally_ae :
    Locally (fun X ↦ ∀ ω, IsCadlag (X · ω)) 𝓕 X P
    ↔ Locally (fun X ↦ ∀ᵐ ω ∂P, IsCadlag (X · ω)) 𝓕 X P := by
  simp_rw [← locally_isCadlag_iff (𝓕 := 𝓕) (P := P),
    locally_locally (HasUsualConditions.toIsRightContinuous P) isStable_isCadlag]

end ConditionallyCompleteLinearOrderBot

end cadlag

end ProbabilityTheory
