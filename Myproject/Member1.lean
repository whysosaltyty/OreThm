import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace TeamOre

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Lemma 1.1.** Every non-Hamiltonian graph `G` is a subgraph of a non-Hamiltonian graph `H`
on the same vertex set such that adding any missing edge to `H` creates a Hamiltonian graph. -/
theorem exists_maximal_nonHamiltonian_supergraph
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ¬ G.IsHamiltonian) :
    ∃ H : SimpleGraph V, G ≤ H ∧ ¬ H.IsHamiltonian ∧
      ∀ u v : V, u ≠ v → ¬ H.Adj u v →
        (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).IsHamiltonian := by
  classical
  suffices key : ∀ n : ℕ, ∀ H : SimpleGraph V, Hᶜ.edgeFinset.card = n → G ≤ H →
      ¬ H.IsHamiltonian → ∃ H' : SimpleGraph V, G ≤ H' ∧ ¬ H'.IsHamiltonian ∧
        ∀ u v : V, u ≠ v → ¬ H'.Adj u v →
          (H' ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).IsHamiltonian from
    key _ G rfl le_rfl hG
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hn hGH hH
    by_cases hmax : ∀ u v : V, u ≠ v → ¬ H.Adj u v →
        (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).IsHamiltonian
    · exact ⟨H, hGH, hH, hmax⟩
    · push Not at hmax
      obtain ⟨u, v, huv, hnadj, hnotham⟩ := hmax
      have hlt : H < H ⊔ SimpleGraph.fromEdgeSet {s(u, v)} := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro heq
        apply hnadj
        rw [heq]
        simp [huv]
      have hcard : (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)})ᶜ.edgeFinset.card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        rw [SimpleGraph.edgeFinset_ssubset_edgeFinset]
        exact compl_lt_compl_iff_lt.mpr hlt
      exact ih _ hcard _ (by convert rfl) (hGH.trans le_sup_left) hnotham

/-- **Lemma 1.2.** If `G ≤ H`, then `dG(v) ≤ dH(v)` for every vertex `v`. -/
theorem degree_mono {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G ≤ H) (v : V) : G.degree v ≤ H.degree v := by
  unfold SimpleGraph.degree
  apply Finset.card_le_card
  intro u hu
  rw [SimpleGraph.mem_neighborFinset] at hu ⊢
  exact hle hu

/-- **Lemma 1.3.** If `P = v₁ ⋯ vₙ` is a Hamiltonian path, then `i ↦ vᵢ` is a bijection from
`{1, ..., n}` to the vertex set, and the reversed path `vₙ ⋯ v₁` is also Hamiltonian. -/
theorem hamiltonianPath_bijective_and_reverse
    {G : SimpleGraph V} {x y : V} (p : G.Walk x y) (hp : p.IsHamiltonian) :
    Function.Bijective p.support.get ∧ p.reverse.IsHamiltonian := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- injective
    exact List.nodup_iff_injective_get.mp
      (List.nodup_iff_count_le_one.mpr fun v => (hp v).le)
  · -- surjective
    intro v
    have hmem : v ∈ p.support :=
      List.count_pos_iff.mp (by rw [hp v]; exact Nat.one_pos)
    exact List.mem_iff_get.mp hmem
  · -- reversed walk is still Hamiltonian
    intro v
    rw [SimpleGraph.Walk.support_reverse, List.count_reverse]
    exact hp v

end TeamOre
