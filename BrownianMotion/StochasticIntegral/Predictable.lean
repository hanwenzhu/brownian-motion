/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Architect
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Adapted

/-!
# Progressively Measurable σ-algebra

This file defines the progressively measurable σ-algebra associated to a filtration, as well as the
notion of predictable processes. We prove that predictable processes are progressively measurable
and adapted. We also give an equivalent characterization of predictability for discrete processes.

## Main definitions

* `Filtration.rightCont`: The right continuation of a filtration.
* `Filtration.Predictable`: The predictable σ-algebra associated to a filtration.
* `Filtration.IsPredictable`: A process is predictable if it is measurable with respect to the
  predictable σ-algebra.

## Main results

* `Filtration.IsPredictable.progMeasurable`: A predictable process is progressively measurable.
* `Filtration.IsPredictable.measurable_succ`: `u` is a discrete predictable process iff
  `u (n + 1)` is `𝓕 n`-measurable and `u 0` is `𝓕 0`-measurable.

## Implementation note

To avoid requiring a `TopologicalSpace` instance on `ι` in the definition of `rightCont`,
we endow `ι` with the order topology `Preorder.topology` inside the definition.
Say you write a statement about `𝓕₊` which does not require a `TopologicalSpace` structure on `ι`,
but you wish to use a statement which requires a topology (such as `rightCont_def`).
Then you can endow `ι` with the order topology by writing
```lean
  letI := Preorder.topology ι
  haveI : OrderTopology ι := ⟨rfl⟩
```

## Notation

* Given a filtration `𝓕`, its right continuation is denoted `𝓕₊` (type `₊` with `;_+`).
-/

open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory.Filtration

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {E : Type*} [TopologicalSpace E]

attribute [blueprint
  "def:filtration"
  (title := "Filtration")
  (statement := /-- A filtration on a measurable space $(\Omega, \mathcal{A})$ with measure $P$
    indexed by a preordered set $T$ is a family of sigma-algebras $\mathcal{F} = (\mathcal{F}_t)_{t
    \in T}$ such that for all $i \le j$, $\mathcal{F}_i \subseteq \mathcal{F}_j$ and for all $t \in
    T$, $\mathcal{F}_t \subseteq \mathcal{A}$. -/)]
  MeasureTheory.Filtration

open scoped Classical in
/-- Given a filtration `𝓕`, its **right continuation** is the filtration `𝓕₊` defined as follows:
- If `i` is isolated on the right, then `𝓕₊ i := 𝓕 i`;
- Otherwise, `𝓕₊ i := ⨅ j > i, 𝓕 j`.
It is sometimes simply defined as `𝓕₊ i := ⨅ j > i, 𝓕 j` when the index type is `ℝ`. In the
general case this is not ideal however. If `i` is maximal for instance, then `𝓕₊ i = ⊤`, which
is inconvenient because `𝓕₊` is not  a `Filtration ι m` anymore. If the index type
is discrete (such as `ℕ`), then we would have `𝓕 = 𝓕₊` (i.e. `𝓕` is right-continuous) only if
`𝓕` is constant.

To avoid requiring a `TopologicalSpace` instance on `ι` in the definition, we endow `ι` with
the order topology `Preorder.topology` inside the definition. Say you write a statement about
`𝓕₊` which does not require a `TopologicalSpace` structure on `ι`,
but you wish to use a statement which requires a topology (such as `rightCont_def`).
Then you can endow `ι` with
the order topology by writing
```lean
  letI := Preorder.topology ι
  haveI : OrderTopology ι := ⟨rfl⟩
``` -/
@[blueprint
  "def:rightLimitFiltration"
  (title := "Right continuation")
  (statement := /-- Assume that $T$ is a partial order. For $\mathcal{F}$ a filtration indexed by
    $T$ and $t \in T$, we define the \emph{right continuation} as
    $$\mathcal{F}_{t+} =
      \begin{cases}
        \mathcal{F}_t, & \text{if $t$ is isolated on the right in the order topology}; \\
        \bigsqcap_{s > t} \mathcal{F}_s, & \text{otherwise}.
      \end{cases}
    $$
    
    Note that $\bigsqcap$ denotes the infimum in the lattice of sigma-algebras on $\Omega$. -/)
  (proof := /-- We endow $T$ with the order topology. Let us first prove that the right continuation
    is nondecreasing. Let $s, t \in T$ such that $s \le t$.
    \begin{itemize}
      \item Suppose $s$ is isolated on the right. Then $\mathcal{F}_{s+} = \mathcal{F}_s$.
      \begin{itemize}
        \item If $t$ is isolated on the right, then $\mathcal{F}_{t+} = \mathcal{F}_t$. Because
        $\mathcal{F}$ is a filtration, we have $\mathcal{F}_s \subseteq \mathcal{F}_t$, and thus
        $\mathcal{F}_{s+} \subseteq \mathcal{F}_{t+}$.
        \item If $t$ is not isolated on the right, then $\mathcal{F}_{t+} = \bigsqcap_{u > t}
        \mathcal{F}_{u}$. Let $u > t$. Then $s \le u$, thus $\mathcal{F}_s \subseteq \mathcal{F}_u$.
        This proves that $\mathcal{F}_s \subseteq \bigsqcap_{u > t}, \mathcal{F}_u$, and thus
        $\mathcal{F}_{s+} \subseteq \mathcal{F}_{t+}$.
      \end{itemize}
      \item Suppose now that $s$ is not isolated on the right, so that $\mathcal{F}_{s+} =
      \bigsqcup_{u > s} \mathcal{F}_u$.
      \begin{itemize}
        \item If $t$ is isolated on the right, then $\mathcal{F}_{t+} = \mathcal{F}_t$. As $s$ is
        not isolated on the right, we deduce that $s \ne t$, and thus $s < t$ because $T$ is a
        partial order. Therefore $\bigsqcap_{u > s} \mathcal{F}_u \subseteq \mathcal{F}_t$, and thus
        $\mathcal{F}_{s+} \subseteq \mathcal{F}_{t+}$.
        \item If $t$ is not isolated on the right, then $\mathcal{F}_{t+} = \bigsqcap_{u > t}
        \mathcal{F}_u$. For any $u > t$, we have $u > s$ and thus $\bigsqcap_{v > s} \mathcal{F}_v
        \subseteq \mathcal{F}_u$, proving that $\bigsqcap_{u > s} \mathcal{F}_u \subseteq
        \bigsqcap_{u > t} \mathcal{F}_u$, and thus $\mathcal{F}_{s+} \subseteq \mathcal{F}_{t+}$.
      \end{itemize}
    \end{itemize}
    
    Turn now to the proof that for all $t \in T$, $\mathcal{F}_{t+} \subseteq \mathcal{A}$. Let $t
    \in T$. If $t$ is isolated on the right, then $\mathcal{F}_{t+} = \mathcal{F}_t \subseteq
    \mathcal{A}$ by definition of a filtration. Otherwise there exists $u > t$, and
    $\mathcal{F}_{t+} \subseteq \mathcal{F}_u \subseteq \mathcal{A}$, so we are done. -/)
  (latexEnv := "definition")]
noncomputable def rightCont [PartialOrder ι] (𝓕 : Filtration ι m) : Filtration ι m :=
  letI : TopologicalSpace ι := Preorder.topology ι
  { seq i := if (𝓝[>] i).NeBot then ⨅ j > i, 𝓕 j else 𝓕 i
    mono' i j hij := by
      simp only [gt_iff_lt]
      split_ifs with hi hj hj
      · exact le_iInf₂ fun k hkj ↦ iInf₂_le k (hij.trans_lt hkj)
      · obtain rfl | hj := eq_or_ne j i
        · contradiction
        · exact iInf₂_le j (lt_of_le_of_ne hij hj.symm)
      · exact le_iInf₂ fun k hk ↦ 𝓕.mono (hij.trans hk.le)
      · exact 𝓕.mono hij
    le' i := by
      split_ifs with hi
      · obtain ⟨j, hj⟩ := (frequently_gt_nhds i).exists
        exact iInf₂_le_of_le j hj (𝓕.le j)
      · exact 𝓕.le i }

@[inherit_doc] scoped postfix:max "₊" => rightCont

open scoped Classical in
@[blueprint
  "lem:rightContDef"
  (statement := /-- Suppose $T$ is a topological space with the topology being the order topology.
    For $t \in T$, the right continuation of $\mathcal{F}$ at $t$ is given by
    $$\mathcal{F}_{t+} =
      \begin{cases}
        \mathcal{F}_t, & \text{if $t$ is isolated on the right}; \\
        \bigsqcap_{s > t} \mathcal{F}_s, & \text{otherwise}.
      \end{cases}
    $$ -/)
  (proof := /-- This follows from Definition~\ref{def:rightLimitFiltration} because the topology on
    $T$ agrees with the one used to define the right continuation. -/)
  (latexEnv := "lemma")]
lemma rightCont_def [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) (i : ι) :
    𝓕₊ i = if (𝓝[>] i).NeBot then ⨅ j > i, 𝓕 j else 𝓕 i := by
  simp only [rightCont, OrderTopology.topology_eq_generate_intervals]

@[blueprint
  "lem:rightContIsolated"
  (statement := /-- Suppose $T$ is a topological space with the topology being the order topology.
    Assume that $t \in T$ is isolated on the right, meaning that there exists a neighbourhood
    $\mathcal{V}$ of $t$ such that $\mathcal{V} \cap \{u \mid u > t\} = \emptyset$. Then
    $\mathcal{F}_{t+} = \mathcal{F}_t$. -/)
  (proof := /-- This is a direct consequence of Lemma~\ref{lem:rightContDef}. -/)
  (latexEnv := "lemma")]
lemma rightCont_eq_of_nhdsGT_eq_bot [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) {i : ι} (hi : 𝓝[>] i = ⊥) :
    𝓕₊ i = 𝓕 i := by
  rw [rightCont_def, hi, neBot_iff, ne_self_iff_false, if_false]

/-- If the index type is a `SuccOrder`, then `𝓕₊ = 𝓕`. -/
@[blueprint
  "lem:rightContSuccOrder"
  (statement := /-- Assume that $T$ is a linear order with successor. This means that for any $t$,
    there is an element $succ(t) \ge t$ such that for any $u > t$, $u \ge succ(t)$, and if $succ(t)
    \le t$, then $t$ is maximal. Then the right continuation of $\mathcal{F}$ is equal to
    $\mathcal{F}$. -/)
  (proof := /-- Endow $T$ with the order topology. In a linear order with successor equipped with
    the order topology, every point is isolated on the right, so we can conclude by
    Lemma~\ref{lem:rightContIsolated}. -/)
  (latexEnv := "lemma")]
lemma rightCont_eq_self [LinearOrder ι] [SuccOrder ι] (𝓕 : Filtration ι m) :
    𝓕₊ = 𝓕 := by
  letI := Preorder.topology ι; haveI : OrderTopology ι := ⟨rfl⟩
  ext _
  rw [rightCont_eq_of_nhdsGT_eq_bot _ SuccOrder.nhdsGT]

@[blueprint
  "lem:rightContIsMax"
  (statement := /-- If $t \in T$ is maximal, $\mathcal{F}_{t+} = \mathcal{F}_t$. -/)
  (proof := /-- Endow $T$ with the order topology. As $t$ is maximal, it is isolated on the right
    for this topology, so we can conclude by Lemma~\ref{lem:rightContIsolated}. -/)
  (latexEnv := "lemma")]
lemma rightCont_eq_of_isMax [PartialOrder ι] (𝓕 : Filtration ι m) {i : ι} (hi : IsMax i) :
    𝓕₊ i = 𝓕 i := by
  letI := Preorder.topology ι; haveI : OrderTopology ι := ⟨rfl⟩
  exact rightCont_eq_of_nhdsGT_eq_bot _ (hi.Ioi_eq ▸ nhdsWithin_empty i)

@[blueprint
  "lem:rightContExistsGt"
  (statement := /-- If $T$ is a linear order and there exists $u > t$ such that $(t, u) =
    \emptyset$, then $\mathcal{F}_{t+} = \mathcal{F}_t$. -/)
  (proof := /-- Endow $T$ with the order topology. The hypothesis implies that $t$ is isolated on
    the right in this topology, so we can conclude by Lemma~\ref{lem:rightContIsolated}. -/)
  (latexEnv := "lemma")]
lemma rightCont_eq_of_exists_gt [LinearOrder ι] (𝓕 : Filtration ι m) {i : ι}
    (hi : ∃ j > i, Set.Ioo i j = ∅) :
    𝓕₊ i = 𝓕 i := by
  letI := Preorder.topology ι; haveI : OrderTopology ι := ⟨rfl⟩
  obtain ⟨j, hij, hIoo⟩ := hi
  have hcov : i ⋖ j := covBy_iff_Ioo_eq.mpr ⟨hij, hIoo⟩
  exact rightCont_eq_of_nhdsGT_eq_bot _ <| CovBy.nhdsGT hcov

/-- If `i` is not isolated on the right, then `𝓕₊ i = ⨅ j > i, 𝓕 j`. This is for instance the case
when `ι` is a densely ordered linear order with no maximal elements and equipped with the order
topology, see `rightCont_eq`. -/
@[blueprint
  "lem:rightContNeBot"
  (statement := /-- Suppose $T$ is a topological space with the topology being the order topology.
    Assume that $t \in T$ is not isolated on the right, meaning that for all neighbourhood
    $\mathcal{V}$ of $t$, $\mathcal{V} \cap \{u | u > t\} \ne \emptyset$. Then $\mathcal{F}_{t+} =
    \bigsqcap_{u > t} \mathcal{F}_u$. -/)
  (proof := /-- This is a direct consequence of Lemma~\ref{lem:rightContDef}. -/)
  (latexEnv := "lemma")]
lemma rightCont_eq_of_neBot_nhdsGT [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) (i : ι) [(𝓝[>] i).NeBot] :
    𝓕₊ i = ⨅ j > i, 𝓕 j := by
  rw [rightCont_def, if_pos ‹(𝓝[>] i).NeBot›]

@[blueprint
  "lem:rightContNotIsMax"
  (statement := /-- Assume that $T$ is a densely ordered linear order, meaning that for all $s < t$,
    there exists $u$ such that $s < u < t$. If $t$ is not maximal, then $\mathcal{F}_{t+} =
    \bigsqcap_{u > t} \mathcal{F}_u$. -/)
  (proof := /-- Endow $T$ with the order topology. In a densely ordered linear order, a point which
    is not maximal is not isolated on the right, so we can conclude by
    Lemma~\ref{lem:rightContNeBot}. -/)
  (latexEnv := "lemma")]
lemma rightCont_eq_of_not_isMax [LinearOrder ι] [DenselyOrdered ι]
    (𝓕 : Filtration ι m) {i : ι} (hi : ¬IsMax i) :
    𝓕₊ i = ⨅ j > i, 𝓕 j := by
  letI := Preorder.topology ι; haveI : OrderTopology ι := ⟨rfl⟩
  have : (𝓝[>] i).NeBot := nhdsGT_neBot_of_exists_gt (not_isMax_iff.mp hi)
  exact rightCont_eq_of_neBot_nhdsGT _ _

/-- If `ι` is a densely ordered linear order with no maximal elements, then no point is isolated
on the right, so that `𝓕₊ i = ⨅ j > i, 𝓕 j` holds for all `i`. This is in particular the
case when `ι := ℝ≥0`. -/
@[blueprint
  "lem:rightContEq"
  (statement := /-- If $T$ is a densely ordered linear order with no maximal element, then forall $t
    \in T$ we have $\mathcal{F}_{t+} = \bigsqcap_{u > t} \mathcal{F}_u$. -/)
  (proof := /-- For all $t$, $t$ is not maximal, so we can conclude by
    Lemma~\ref{lem:rightContNotIsMax}. -/)
  (latexEnv := "lemma")]
lemma rightCont_eq [LinearOrder ι] [DenselyOrdered ι] [NoMaxOrder ι]
    (𝓕 : Filtration ι m) (i : ι) :
    𝓕₊ i = ⨅ j > i, 𝓕 j := 𝓕.rightCont_eq_of_not_isMax (not_isMax i)

variable [PartialOrder ι]

@[blueprint
  "lem:leRightCont"
  (statement := /-- The filtration $\mathcal{F}$ is contained in its right continuation. -/)
  (proof := /-- Endow $T$ with the order topology, and consider $t \in T$. Using
    Lemma~\ref{lem:rightContDef}, we split into two cases. If $t$ is isolated on the right, then
    $\mathcal{F}_{t+} = \mathcal{F}_t \supseteq \mathcal{F}_t$ and we are done. Otherwise, for all
    $u > t$, $\mathcal{F}_t \subseteq \mathcal{F}_u$, therefore $\mathcal{F}_t \subseteq
    \bigsqcap_{u > t} \mathcal{F}_u$, and we are done. -/)
  (latexEnv := "lemma")]
lemma le_rightCont (𝓕 : Filtration ι m) : 𝓕 ≤ 𝓕₊ := by
  letI := Preorder.topology ι; haveI : OrderTopology ι := ⟨rfl⟩
  intro i
  by_cases hne : (𝓝[>] i).NeBot
  · rw [rightCont_eq_of_neBot_nhdsGT]
    exact le_iInf₂ fun _ he => 𝓕.mono he.le
  · rw [rightCont_def, if_neg hne]

@[blueprint
  "lem:rightContSelf"
  (statement := /-- The right continuation of the right continuation of $\mathcal{F}$ is equal to
    the right continuation of $\mathcal{F}$. -/)
  (proof := /-- Let $t \in T$. From Lemma~\ref{lem:leRightCont}, we already now that
    $\mathcal{F}_{t+} \subseteq \mathcal{F}_{t++}$. Endow $T$ with the order topology and split
    according to Lemma~\ref{lem:rightContDef}. If $t$ is isolated on the right, then
    $\mathcal{F}_{t++} = \mathcal{F}_{t+}$ and we are done. Otherwise consider $u > t$. Then there
    exists $v \in T$ such that $t < v < u$. If $v$ is not isolated on the right then
    $$\mathcal{F}_{t++} = \bigsqcap_{s > t} \mathcal{F}_{s+} \subseteq \mathcal{F}_{v+} =
    \bigsqcap_{s > v} \mathcal{F}_s \subseteq \mathcal{F}_u,$$
    and otherwise
    $$\mathcal{F}_{t++} = \bigsqcap_{s > t} \mathcal{F}_{s+} \subseteq \mathcal{F}_{v+} =
    \mathcal{F}_v \subseteq \mathcal{F}_u,$$
    thus $\mathcal{F}_{t++} \subseteq \bigsqcap_{s > t} \mathcal{F}_s = \mathcal{F}_{t+}$, which
    concludes the proof. -/)
  (latexEnv := "lemma")]
lemma rightCont_self (𝓕 : Filtration ι m) : 𝓕₊₊ = 𝓕₊ := by
  letI := Preorder.topology ι; haveI : OrderTopology ι := ⟨rfl⟩
  apply le_antisymm _ 𝓕₊.le_rightCont
  intro i
  by_cases hne : (𝓝[>] i).NeBot
  · have hineq : (⨅ j > i, 𝓕₊ j) ≤ ⨅ j > i, 𝓕 j := by
      apply le_iInf₂ fun u hu => ?_
      have hiou : Set.Ioo i u ∈ 𝓝[>] i := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨Set.Iio u, (isOpen_Iio' u).mem_nhds hu, fun _ hx ↦ ⟨hx.2, hx.1⟩⟩
      obtain ⟨v, hv⟩ := hne.nonempty_of_mem hiou
      have hle₁ : (⨅ j > i, 𝓕₊ j) ≤ 𝓕₊ v := iInf₂_le_of_le v hv.1 le_rfl
      have hle₂ : 𝓕₊ v ≤ 𝓕 u := by
        by_cases hnv : (𝓝[>] v).NeBot
        · simpa [rightCont_eq_of_neBot_nhdsGT] using iInf₂_le_of_le u hv.2 le_rfl
        · simpa [rightCont_def, hnv] using 𝓕.mono hv.2.le
      exact hle₁.trans hle₂
    simpa [rightCont_eq_of_neBot_nhdsGT] using hineq
  · rw [rightCont_def, if_neg hne]

/-- A filtration `𝓕` is right continuous if it is equal to its right continuation `𝓕₊`. -/
@[blueprint
  "def:rightContinuous"
  (title := "Right-continuous filtration")
  (statement := /-- We say that the filtration is \emph{right-continuous} if for all $t \in T$,
    $\mathcal{F}_{t+} \subseteq \mathcal{F}_t$. -/)]
class IsRightContinuous (𝓕 : Filtration ι m) where
    /-- The right continuity property. -/
    RC : 𝓕₊ ≤ 𝓕

@[blueprint
  "lem:eqRightCont"
  (statement := /-- If $\mathcal{F}$ is right-continuous, then for all $t \in T$, $\mathcal{F}_t =
    \mathcal{F}_{t+}$. -/)
  (proof := /-- This is a direct consequence of Definition~\ref{def:rightContinuous} and
    Lemma~\ref{lem:leRightCont}. -/)
  (latexEnv := "lemma")]
lemma IsRightContinuous.eq {𝓕 : Filtration ι m} [h : IsRightContinuous 𝓕] :
    𝓕 = 𝓕₊ := le_antisymm 𝓕.le_rightCont h.RC

@[blueprint
  "lem:rightContinuousRightCont"
  (statement := /-- The right continuation of $\mathcal{F}$ is right-continuous. -/)
  (proof := /-- This follows immediately from Lemma~\ref{lem:rightContSelf}. -/)
  (latexEnv := "lemma")]
lemma isRightContinuous_rightCont (𝓕 : Filtration ι m) : 𝓕₊.IsRightContinuous :=
  ⟨(rightCont_self 𝓕).le⟩

@[blueprint
  "lem:rightContinuousMeasurableSet"
  (statement := /-- If $\mathcal{F}$ is right-continuous, then for all $t \in T$, any set $A
    \subseteq \Omega$ which is $\mathcal{F}_t$-measurable is also $\mathcal{F}_{t+}$-measurable. -/)
  (proof := /-- This is a direct consequence of Definition~\ref{def:rightContinuous}. -/)
  (latexEnv := "lemma")]
lemma IsRightContinuous.measurableSet {𝓕 : Filtration ι m} [IsRightContinuous 𝓕] {i : ι}
    {s : Set Ω} (hs : MeasurableSet[𝓕₊ i] s) :
    MeasurableSet[𝓕 i] s := IsRightContinuous.eq (𝓕 := 𝓕) ▸ hs

/-- A filtration `𝓕` is said to satisfy the usual conditions if it is right continuous and `𝓕 0`
  and consequently `𝓕 t` is complete (i.e. contains all null sets) for all `t`. -/
@[blueprint
  "def:hasUsualConditions"
  (title := "Usual conditions")
  (statement := /-- We say that a filtered probability space $(\Omega, \mathcal{F}, P)$ satisfies
    the usual conditions if the filtration is right-continuous and if $\mathcal{F}_0$ contains all
    the $P$-null sets. -/)]
class HasUsualConditions [OrderBot ι] (𝓕 : Filtration ι m) (μ : Measure Ω := by volume_tac)
    extends IsRightContinuous 𝓕 where
    /-- `𝓕 ⊥` contains all the null sets. -/
    IsComplete ⦃s : Set Ω⦄ (hs : μ s = 0) : MeasurableSet[𝓕 ⊥] s

variable [OrderBot ι]

instance {𝓕 : Filtration ι m} {μ : Measure Ω} [u : HasUsualConditions 𝓕 μ] {i : ι} :
    @Measure.IsComplete Ω (𝓕 i) (μ.trim <| 𝓕.le _) :=
  ⟨fun _ hs ↦ 𝓕.mono bot_le _ <| u.2 (measure_eq_zero_of_trim_eq_zero (Filtration.le 𝓕 _) hs)⟩

lemma HasUsualConditions.measurableSet_of_null
    (𝓕 : Filtration ι m) {μ : Measure Ω} [u : HasUsualConditions 𝓕 μ] (s : Set Ω) (hs : μ s = 0) :
    MeasurableSet[𝓕 ⊥] s :=
  u.2 hs

end MeasureTheory.Filtration
