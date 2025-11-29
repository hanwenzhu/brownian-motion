/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Thomas Zhu
-/
import Architect
import BrownianMotion.Auxiliary.Jensen
import Mathlib.Probability.Martingale.Basic

/-! # Properties of martingales and submartingales
-/

namespace MeasureTheory

section

variable {ι Ω E : Type*} [Preorder ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E} {𝓕 : Filtration ι mΩ}

@[blueprint
  "lem:Martingale.congr"
  (statement := /-- If $X$ is a martingale and $Y$ is an adapted modification of $X$, then $Y$ is a
    martingale. -/)
  (proof := /-- Let $i \le j$ in $T$. We want to show that $P[Y_j \mid \mathcal{F}_i] = Y_i$ almost
    surely.
    It suffices to show that $\int_A Y_j \: dP = \int_A Y_i \: dP$ for all $A \in \mathcal{F}_i$.
    Let then $A \in \mathcal{F}_i$.
    \begin{align*}
      \int_A Y_j \: dP
      &= \int_A X_j \: dP
      = \int_A X_i \: dP
      = \int_A Y_i \: dP
      \: .
    \end{align*} -/)
  (latexEnv := "lemma")]
lemma Martingale.congr (hX : Martingale X 𝓕 P) (hY : Adapted 𝓕 Y) (h_eq : ∀ t, X t =ᵐ[P] Y t) :
    Martingale Y 𝓕 P := by
  refine ⟨hY, fun i j hij ↦ ?_⟩
  calc
    P[Y j | 𝓕 i] =ᵐ[P] P[X j | 𝓕 i] := (condExp_congr_ae (h_eq j)).symm
    _ =ᵐ[P] Y i := (hX.2 i j hij).trans (h_eq i)

@[blueprint
  "lem:Submartingale.congr"
  (statement := /-- If $X$ is a submartingale and $Y$ is an adapted modification of $X$, then $Y$ is
    a submartingale. -/)
  (proof := /-- Let $i \le j$ in $T$. We want to show that $P[Y_j \mid \mathcal{F}_i] \ge Y_i$
    almost surely.
    It suffices to show that $\int_A Y_j \: dP \ge \int_A Y_i \: dP$ for all $A \in \mathcal{F}_i$.
    Let then $A \in \mathcal{F}_i$.
    \begin{align*}
      \int_A Y_j \: dP
      &= \int_A X_j \: dP
      \ge \int_A X_i \: dP
      = \int_A Y_i \: dP
      \: .
    \end{align*} -/)
  (latexEnv := "lemma")]
lemma Submartingale.congr [LE E] (hX : Submartingale X 𝓕 P) (hY : Adapted 𝓕 Y)
    (h_eq : ∀ t, X t =ᵐ[P] Y t) :
    Submartingale Y 𝓕 P := by
  refine ⟨hY, ?_, ?_⟩
  · intro i j hij
    have hcond : P[X j | 𝓕 i] =ᵐ[P] P[Y j | 𝓕 i] := condExp_congr_ae (h_eq j)
    exact (Filter.eventuallyLE_congr (h_eq i) hcond).mp (ae_le_condExp hX hij)
  · exact fun i ↦ (integrable_congr (h_eq i)).mp (hX.integrable i)

lemma Martingale.indicator [OrderBot ι] {s : Set Ω}
    (hX : Martingale X 𝓕 P) (hs : MeasurableSet[𝓕 ⊥] s) :
    Martingale (fun t ↦ s.indicator (X t)) 𝓕 P :=
  ⟨fun i ↦ (hX.adapted i).indicator (𝓕.mono bot_le _ hs), fun i j hij ↦
    (condExp_indicator (hX.integrable _) (𝓕.mono bot_le _ hs)).trans (hX.2 i j hij).indicator⟩

end

variable {ι Ω E : Type*} [LinearOrder ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [SigmaFinite P] {X Y : ι → Ω → E} {𝓕 : Filtration ι mΩ}

attribute [blueprint
  "def:Martingale"
  (title := "Martingale")
  (statement := /-- Let $\mathcal{F}$ be a filtration on a measurable space $\Omega$ with measure
    $P$ indexed by $T$.
    A family of functions $M : T \to \Omega \to E$ is a martingale with respect to a filtration
    $\mathcal{F}$ if $M$ is adapted with respect to $\mathcal{F}$ and for all $i \le j$, $P[M_j \mid
    \mathcal{F}_i] = M_i$ almost surely. -/)]
  MeasureTheory.Martingale

attribute [blueprint
  "def:Submartingale"
  (title := "Submartingale")
  (statement := /-- Let $\mathcal{F}$ be a filtration on a measurable space $\Omega$ with measure
    $P$ indexed by $T$.
    A family of functions $M : T \to \Omega \to E$ is a submartingale with respect to a filtration
    $\mathcal{F}$ if $M$ is adapted with respect to $\mathcal{F}$ and for all $i \le j$, $P[M_j \mid
    \mathcal{F}_i] \ge M_i$ almost surely. -/)]
  MeasureTheory.Submartingale

@[blueprint
  "lem:Martingale.submartingale_convex_comp"
  (statement := /-- Let $X : T \rightarrow \Omega\rightarrow E$ a martingale with values in a normed
    space $E$.
    Let $\phi : E \rightarrow \mathbb{R}$ convex and continuous such that
    $\phi(X_t)\in L^1(\Omega)$ for every $t\in T$. Then $\phi(X)$ is a sub-martingale. -/)
  (proof := /-- % See 1.4.12 Pascucci
    By the conditional Jensen inequality (Lemma~\ref{lem:conditional_jensen}),
    $\phi(X_t) = \phi\left( \mathbb{E}[X_T\ |\ \mathcal{F}_t] \right)\leq \mathbb{E}[\phi(X_T)\ |\
    \mathcal{F}_t]$. -/)
  (latexEnv := "lemma")]
lemma Martingale.submartingale_convex_comp (hX : Martingale X 𝓕 P) {φ : E → ℝ}
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : Continuous φ)
    (hφ_int : ∀ t, Integrable (fun ω ↦ φ (X t ω)) P) :
    Submartingale (fun t ω ↦ φ (X t ω)) 𝓕 P := by
  refine ⟨fun i ↦ hφ_cont.comp_stronglyMeasurable (hX.adapted i), fun i j hij ↦ ?_, hφ_int⟩
  calc
    _ =ᵐ[P] fun ω ↦ φ (P[X j | 𝓕 i] ω) := hX.condExp_ae_eq hij |>.fun_comp φ |>.symm
    _ ≤ᵐ[P] P[fun ω ↦ φ (X j ω) | 𝓕 i] :=
      conditional_jensen (𝓕.le i) hφ_cvx hφ_cont.lowerSemicontinuous (hX.integrable j) (hφ_int j)

@[blueprint
  "cor:Martingale.submartingale_norm"
  (statement := /-- Let $X : T \rightarrow \Omega \rightarrow E$ a martingale with values in a
    normed space $E$.
    Then $\Vert X \Vert$ is a sub-martingale. -/)
  (proof := /-- Same proof as Lemma~\ref{lem:Martingale.submartingale_convex_comp}, specialized to
    $\phi = \Vert \cdot \Vert$, for which we can use Corollary~\ref{cor:norm_condExp_le}. -/)
  (latexEnv := "corollary")]
lemma Martingale.submartingale_norm (hX : Martingale X 𝓕 P) :
    Submartingale (fun t ω ↦ ‖X t ω‖) 𝓕 P :=
  hX.submartingale_convex_comp convexOn_univ_norm continuous_norm fun i ↦ (hX.integrable i).norm

@[blueprint
  "lem:convex_of_submg_is_submg"
  (statement := /-- Let $X : T  \rightarrow \Omega \rightarrow E$ a sub-martingale.
    Let $\phi:E \rightarrow \mathbb{R}$ convex, continuous, and increasing such that
    $\phi(X_t)\in L^1(\Omega)$ for every $t\in T$. Then $\phi(X)$ is a sub-martingale. -/)
  (proof := /-- By Jensen and the fact that $\phi$ is increasing
    $\phi(X_t) \leq \phi\left( \mathbb{E}[X_T\ |\ \mathcal{F}_t] \right)\leq \mathbb{E}[\phi(X_T)\
    |\ \mathcal{F}_t]$. -/)
  (latexEnv := "lemma")]
lemma Submartingale.monotone_convex_comp [Preorder E] (hX : Submartingale X 𝓕 P) {φ : E → ℝ}
    (hφ_mono : Monotone φ) (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : Continuous φ)
    (hφ_int : ∀ t, Integrable (fun ω ↦ φ (X t ω)) P) :
    Submartingale (fun t ω ↦ φ (X t ω)) 𝓕 P := by
  refine ⟨fun i ↦ hφ_cont.comp_stronglyMeasurable (hX.adapted i), fun i j hij ↦ ?_, hφ_int⟩
  calc
    _ ≤ᵐ[P] fun ω ↦ φ (P[X j | 𝓕 i] ω) := (hX.ae_le_condExp hij).mono fun ω hω ↦ hφ_mono hω
    _ ≤ᵐ[P] P[fun ω ↦ φ (X j ω) | 𝓕 i] :=
      conditional_jensen (𝓕.le i) hφ_cvx hφ_cont.lowerSemicontinuous (hX.integrable j) (hφ_int j)

end MeasureTheory
