import MA4N1.Init
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import mathlib.combinatorics.simplegraph.cyclegraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Fin.Basic

open SimpleGraph

#check SimpleGraph.completeGraph

variable (n : ℕ)

/- V = V(G) size, Fintype for V to have finite cardinality, DecidableEq for vertex comparison-/

example : SimpleGraph (Fin n) := cycleGraph n

lemma cyclegraph_npath_iscycle (v : Fin n) (p : (cycleGraph n).Walk v v) (hn : 3 ≤ n)
    (ht : p.IsTrail) (hp : p.length = n) : p.IsCycle := by
      rw [Walk.isCycle_def]
      refine ⟨ht, ?_, ?_⟩
      have hnil : p ≠ Walk.nil := fun h => by
       subst h
       simp at hp
       omega
      exact hnil
      refine List.nodup_iff_count_of_mem.mpr ?_
      refine fun a ha ↦ ?_
      sorry

lemma cyclegraph_npath_hamilt (G := cycleGraph n) (h : 3 ≤ n) : G.IsHamiltonian := by
    sorry


lemma CompleteGraph_Hamiltonian (h: 3 ≤ n)
    (G := completeGraph (Fin n)): G.IsHamiltonian:= by
  exact cyclegraph_npath_hamilt n G h

#check IsHamiltonian

theorem OreTheorem (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h: 3 ≤ n) (ore: ∀ u v : Fin n, u ≠ v → ¬ G.Adj u v → G.degree u + G.degree v ≥ n):
    G.IsHamiltonian := by
  sorry
