/-
Member 2: Hamiltonian path extraction

* Lemma 2.1 `exists_ne_not_adj_of_not_isHamiltonian`:
  every non-Hamiltonian graph on `n ≥ 3` vertices has two distinct non-adjacent vertices.
* Lemma 2.2 `exists_isHamiltonian_walk_of_isHamiltonian_sup_edge`:
  if `H` is non-Hamiltonian, `x ≠ y`, `x` and `y` are non-adjacent, and `H + xy` is Hamiltonian,
  then `H` has a Hamiltonian path from `x` to `y`.

Lemma 4.1 (`Kₙ` is Hamiltonian for `n ≥ 3`) is already in Mathlib as
`SimpleGraph.isHamiltonian_top`, so Lemma 2.1 uses it directly.
-/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Operations

namespace Ore

open SimpleGraph

variable {V : Type*}

/-! ## Lemma 2.1 -/

/-- **Lemma 2.1.** A non-Hamiltonian graph on at least 3 vertices has two distinct
non-adjacent vertices.

The hypothesis `3 ≤ Fintype.card V` is needed: on 2 vertices, `K₂` is not Hamiltonian but has
no non-adjacent pair. -/
theorem exists_ne_not_adj_of_not_isHamiltonian [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hcard : 3 ≤ Fintype.card V) (hG : ¬ G.IsHamiltonian) :
    ∃ u v : V, u ≠ v ∧ ¬ G.Adj u v := by
  by_contra h
  push Not at h
  have hG_top : G = ⊤ := by
    ext u v
    rw [top_adj]
    exact ⟨G.ne_of_adj, h u v⟩
  apply hG
  rw [hG_top]
  exact isHamiltonian_top hcard

/-! ## Helper lemmas for Lemma 2.2 -/

/-- An edge of `H ⊔ edge x y` other than `s(x, y)` is an edge of `H`. -/
theorem mem_edgeSet_of_mem_edgeSet_sup_edge {H : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    {e : Sym2 V} (he : e ∈ (H ⊔ edge x y).edgeSet) (hne : e ≠ s(x, y)) :
    e ∈ H.edgeSet := by
  rw [edgeSet_sup, edgeSet_edge_of_ne hxy] at he
  rcases he with he | he
  · exact he
  · exact absurd (Set.mem_singleton_iff.mp he) hne

/-- In a path starting at `x`, the only edge at `x` is the first one:
if `s(x, y)` is an edge of the path, then the second vertex of the path is `y`. -/
theorem snd_eq_of_isPath_of_mem_edges {G : SimpleGraph V} {x y z : V} {p : G.Walk x z}
    (hp : p.IsPath) (h : s(x, y) ∈ p.edges) : p.snd = y := by
  cases p with
  | nil => simp at h
  | cons hadj r =>
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.edges_cons, List.mem_cons] at h
    rcases h with h | h
    · rw [Walk.snd_cons]
      exact (Sym2.congr_right.mp h).symm
    · exact absurd (r.fst_mem_support_of_mem_edges h) hp.2

/-- The edge list of a non-empty walk is its first edge followed by the edges of its tail. -/
theorem edges_eq_cons_edges_tail {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬ p.Nil) :
    p.edges = s(u, p.snd) :: p.tail.edges := by
  conv_lhs => rw [← p.cons_tail_eq hp]
  rw [Walk.edges_cons]

/-- Core of Lemma 2.2: if a Hamiltonian cycle `c` of `H ⊔ edge x y` starts with the step `x → y`,
then deleting that first edge leaves a Hamiltonian path of `H` from `y` to `x`;
reversing it gives a Hamiltonian path of `H` from `x` to `y`. -/
theorem exists_isHamiltonian_walk_of_snd_eq [DecidableEq V] {H : SimpleGraph V} {x y : V}
    (hxy : x ≠ y)
    (c : (H ⊔ edge x y).Walk x x) (hc : c.IsHamiltonianCycle) (hsnd : c.snd = y) :
    ∃ p : H.Walk x y, p.IsHamiltonian := by
  have hnil : ¬ c.Nil := hc.not_nil
  have hnodup : c.edges.Nodup := hc.edges_nodup
  rw [edges_eq_cons_edges_tail c hnil, List.nodup_cons] at hnodup
  have hnotmem : s(x, y) ∉ c.tail.edges := by
    intro h
    apply hnodup.1
    convert h using 2
  have hsub : ∀ e ∈ c.tail.edges, e ∈ H.edgeSet := by
    intro e he
    apply mem_edgeSet_of_mem_edgeSet_sup_edge hxy (c.tail.edges_subset_edgeSet he)
    rintro rfl
    exact hnotmem he
  refine ⟨((c.tail.transfer H hsub).reverse).copy rfl hsnd, ?_⟩
  rw [Walk.isHamiltonian_copy, Walk.isHamiltonian_reverse, Walk.isHamiltonian_transfer]
  exact hc.isHamiltonian_tail

/-! ## Lemma 2.2 -/

/-- **Lemma 2.2.** If `H` is not Hamiltonian, `x ≠ y` are non-adjacent, and `H + xy` is
Hamiltonian, then `H` has a Hamiltonian path from `x` to `y`.

(The hypothesis `¬ H.Adj x y` is not actually used in the proof: if `x` and `y` were adjacent,
then `H ⊔ edge x y = H` and the hypotheses would contradict each other. It is kept so the
statement matches the outline.) -/
theorem exists_isHamiltonian_walk_of_isHamiltonian_sup_edge [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {x y : V}
    (hxy : x ≠ y) (_hnadj : ¬ H.Adj x y) (hH : ¬ H.IsHamiltonian)
    (hH' : (H ⊔ edge x y).IsHamiltonian) :
    ∃ p : H.Walk x y, p.IsHamiltonian := by
  have : Nontrivial V := ⟨⟨x, y, hxy⟩⟩
  -- Step 1: take a Hamiltonian cycle `c` of `H + xy` based at `x`.
  obtain ⟨c, hc⟩ := hH'.exists_isHamiltonianCycle x
  have hnil : ¬ c.Nil := hc.not_nil
  -- Step 2: `c` must use the new edge `xy`, otherwise it would be a Hamiltonian cycle of `H`.
  have hmem : s(x, y) ∈ c.edges := by
    by_contra hnotmem
    have hsub : ∀ e ∈ c.edges, e ∈ H.edgeSet := by
      intro e he
      apply mem_edgeSet_of_mem_edgeSet_sup_edge hxy (c.edges_subset_edgeSet he)
      rintro rfl
      exact hnotmem he
    exact hH ((Walk.isHamiltonianCycle_transfer hsub).mpr hc).isHamiltonian
  -- Step 3: since `x` is the base point, the edge `xy` is either the first or the last edge of `c`.
  by_cases hsnd : c.snd = y
  · -- `xy` is the first edge.
    exact exists_isHamiltonian_walk_of_snd_eq hxy c hc hsnd
  · -- `xy` is the last edge, so it is the first edge of the reversed cycle.
    have hmem_tail : s(x, y) ∈ c.tail.edges := by
      rw [edges_eq_cons_edges_tail c hnil, List.mem_cons] at hmem
      rcases hmem with h | h
      · exact absurd (Sym2.congr_right.mp h).symm hsnd
      · exact h
    have hpath : c.tail.reverse.IsPath := hc.isHamiltonian_tail.isPath.reverse
    have hmem_rev : s(x, y) ∈ c.tail.reverse.edges := by
      rw [Walk.edges_reverse, List.mem_reverse]
      exact hmem_tail
    have hpen : c.tail.reverse.snd = y := snd_eq_of_isPath_of_mem_edges hpath hmem_rev
    have hlen : c.length ≠ 1 := by
      have := hc.three_le_length
      omega
    rw [Walk.snd_reverse, Walk.penultimate_tail_eq_penultimate hlen] at hpen
    apply exists_isHamiltonian_walk_of_snd_eq hxy c.reverse hc.reverse
    rw [Walk.snd_reverse]
    exact hpen

end Ore
