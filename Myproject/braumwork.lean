import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Fin.Basic

/-! Siraphob Buahong (braum)'s work for the project. -/
open SimpleGraph

#check SimpleGraph.completeGraph
#check SimpleGraph.IsHamiltonian
#check Walk.IsHamiltonian.isHamiltonian_of_adj

variable {V : Type*}

/- V = V(G) size, Fintype for V to have finite cardinality, DecidableEq for vertex comparison-/



-- for s ≤ v there is a path from a to b with length s in the complete graph.
-- for some a b and path between, it is a path and vertices on p are 'in s' i.e. path has length s.
lemma exists_path_with_support (s : Finset V) :
    s = ∅ ∨ ∃ (a b : V) (p : (⊤ : SimpleGraph V).Walk a b),
      p.IsPath ∧ ∀ v, v ∈ p.support ↔ v ∈ s := by
      classical
      refine Finset.induction_on s (Or.inl rfl) ?_
      intro x s hx ih
      right
      rcases ih with rfl | ⟨a, b, p, hp, hsupp⟩
      · exact ⟨x, x, Walk.nil, Walk.IsPath.nil, by exact fun v ↦ Eq.to_iff rfl⟩
      · have hxs : x ∉ p.support := fun h => hx ((hsupp x).1 h)
        have hxa : x ≠ a := fun h => hx (by rw [h]; exact (hsupp a).1 p.start_mem_support)
        have hadj : (⊤ : SimpleGraph V).Adj x a := by simpa using hxa
        refine ⟨x, b, Walk.cons hadj p, ?_, ?_⟩
        · exact Walk.IsPath.cons hp hxs
        · intro v
          grind
      done

theorem complete_isHamiltonian [Fintype V] [DecidableEq V] (hn : 3 ≤ Fintype.card V) :
    (⊤ : SimpleGraph V).IsHamiltonian := by
  rcases exists_path_with_support (Finset.univ : Finset V) with h0 | ⟨a, b, p, hp, hsupp⟩
  · have := congrArg Finset.card h0
    grind
  · have hham : p.IsHamiltonian := hp.isHamiltonian_of_mem fun v => (hsupp v).2 (Finset.mem_univ v)
    have hlen := hham.length_eq
    have hab : a ≠ b := by
      rintro rfl
      have hnil : p.Nil := Walk.isPath_iff_nil.1 hp
      grind
    exact hham.isHamiltonian_of_adj (by simpa using hab) (by grind)
    done

#check IsHamiltonian

--contra of deg_bound

lemma deg_bound' {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (v : Fin (n + 1) ≃ V)
    (hlt : n < G.degree (v 0) + G.degree (v (Fin.last n))) :
    ∃ i : Fin n, G.Adj (v 0) (v i.succ) ∧ G.Adj (v i.castSucc) (v (Fin.last n)) := by
--two neighbor sets for v0 and vn
  obtain ⟨S, hSmem⟩ : ∃ S : Finset (Fin n),
      ∀ i, i ∈ S ↔ G.Adj (v 0) (v i.succ) :=
    ⟨Finset.univ.filter (fun i => G.Adj (v 0) (v i.succ)), fun i => by simp⟩
  obtain ⟨T, hTmem⟩ : ∃ T : Finset (Fin n),
      ∀ i, i ∈ T ↔ G.Adj (v i.castSucc) (v (Fin.last n)) :=
    ⟨Finset.univ.filter (fun i => G.Adj (v i.castSucc) (v (Fin.last n))), fun i => by simp⟩
--|S| = deg.v0
  have hS : S.card = G.degree (v 0) := by
    rw [← G.card_neighborFinset_eq_degree (v 0)]
    apply Finset.card_bij (fun i _ => v i.succ)
    · intro i hi
      rw [SimpleGraph.mem_neighborFinset]
      grind
    · intro i _ j _ hij
      exact Fin.succ_injective _ (v.injective hij)
    · intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      obtain ⟨k, rfl⟩ := v.surjective w
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · grind
      · grind
--|T| = deg.vn, same strat as before
  have hT : T.card = G.degree (v (Fin.last n)) := by
    rw [← G.card_neighborFinset_eq_degree (v (Fin.last n))]
    apply Finset.card_bij (fun i _ => v i.castSucc)
    · intro i hi
      rw [SimpleGraph.mem_neighborFinset]
      exact ((hTmem i).mp hi).symm
    · intro i _ j _ hij
      exact Fin.castSucc_injective _ (v.injective hij)
    · intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      obtain ⟨k, rfl⟩ := v.surjective w
      rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
      · exact ⟨i, (hTmem i).mpr hw.symm, rfl⟩
      · grind
--the rest (pigeonhole for S ∩ T)
  have hU := Finset.card_union_add_card_inter S T
  have hle : (S ∪ T).card ≤ n := by simpa using Finset.card_le_univ (S ∪ T)
  have hpos : 0 < (S ∩ T).card := by grind
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_inter] at hi
  exact ⟨i, (hSmem i).mp hi.1, (hTmem i).mp hi.2⟩
  done

lemma deg_bound {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (v : Fin (n + 1) ≃ V)
    (h : ∀ i : Fin n,
      ¬ (G.Adj (v 0) (v i.succ) ∧ G.Adj (v i.castSucc) (v (Fin.last n)))) :
    G.degree (v 0) + G.degree (v (Fin.last n)) ≤ n := by
  by_contra hlt
  obtain ⟨i, hi⟩ := deg_bound' G n v (by grind)
  exact h i hi
  done

theorem OreTheorem_v (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
(h : 3 ≤ Fintype.card V) (ore : ∀ u v : V, u ≠ v → ¬ G.Adj u v → G.degree u + G.degree v ≥ n):
    G.IsHamiltonian := by
  sorry
