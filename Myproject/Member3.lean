import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic


open SimpleGraph

--check
#check Nat.sub_add_cancel

#check Walk.take
#check Walk.drop
#check Walk.reverse
#check Walk.cons
#check Walk.append

#check Walk.support_append
#check Walk.support_cons
#check Walk.support_take
#check Walk.support_reverse
#check Walk.drop_support_eq_support_drop_min

#check List.reverse_perm
#check List.Perm.append_left
#check List.Perm.count_eq
#check List.take_append_drop

#check Walk.IsHamiltonian.length_eq
#check Walk.IsHamiltonian.isPath
#check Walk.isPath_copy
#check Walk.isCycle_iff_isPath_tail_and_le_length
#check Walk.isHamiltonianCycle_iff_isCycle_and_length_eq

namespace TeamOre

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V)

-- Lemma 3.1: Construction of a Hamiltonian cycle
theorem cycle_construction
    {x y : V}
    (p : H.Walk x y)
    (hp : p.IsHamiltonian)
    (hn : 3 ≤ Fintype.card V)
    (j : ℕ)
    (hj₁ : 1 ≤ j)
    (hj₂ : j ≤ p.length)
    (hx : H.Adj x (p.getVert j))
    (hy : H.Adj (p.getVert (j - 1)) y) :
    H.IsHamiltonian := by
--
  -- Step 1: Arithmetic of indices
  have hj : j - 1 + 1 = j := by
    -- simp
    -- exact?
    apply Nat.sub_add_cancel
    exact hj₁
--

  -- Step 2: Construct the first part of the new walk
  let p₁ : H.Walk x (p.getVert (j - 1)) :=
    p.take (j - 1)
--

  -- Step 3: Construct the reversed part of the walk
  let p₂ : H.Walk y (p.getVert j) :=
    (p.drop j).reverse
--

  -- Step 4: Add the edge from p.getVert (j - 1) to y
  let p₃ : H.Walk (p.getVert (j - 1)) (p.getVert j) :=
    Walk.cons hy p₂
--

  -- Step 5: Join the two parts together
  -- let q := p₁.append p₂
  -- The endpoints do not match.
--
  let q : H.Walk x (p.getVert j) :=
    p₁.append p₃
--

  -- Step 6: Describe the support of q
  have hs : q.support =
      p.support.take j ++ (p.support.drop j).reverse := by
--
    -- simp [q, p₁, p₂, p₃]
    simp only [q, p₁, p₂, p₃]
    rw [Walk.support_append]
    rw [Walk.support_cons]
    rw [List.tail_cons]
    rw [Walk.support_take]
    rw [Walk.support_reverse]
    rw [Walk.drop_support_eq_support_drop_min]
--
    -- Need to use the upper bound on j.
    rw [Nat.min_eq_left hj₂]
    rw [hj]
--

  -- Step 7: Reversing a list preserves its elements
  have hreverse :
      (p.support.drop j).reverse.Perm
        (p.support.drop j) := by
    exact List.reverse_perm (p.support.drop j)
--

  -- Step 8: Append the first part to both lists
  have happend :
      (p.support.take j ++ (p.support.drop j).reverse).Perm
        (p.support.take j ++ p.support.drop j) := by
    apply List.Perm.append_left
    exact hreverse
--

  -- Step 9: The supports of p and q are permutations
  have hperm : q.support.Perm p.support := by
    rw [hs]
    -- exact happend
    rw [List.take_append_drop] at happend
    exact happend
--

  -- Step 10: Show that q is Hamiltonian
  have hq : q.IsHamiltonian := by
--
    -- exact hp
    rw [Walk.IsHamiltonian] at hp
    rw [Walk.IsHamiltonian]
    intro v
--
    -- exact hp v
    -- Use the fact that permutations preserve counts.
    rw [hperm.count_eq v]
    exact hp v
--

  -- Step 11: Reverse the direction of the closing edge
  have hx' : H.Adj (p.getVert j) x := by
    apply H.adj_symm
    exact hx
--

  -- Step 12: Construct a closed walk
  let c : H.Walk (p.getVert j) (p.getVert j) :=
    Walk.cons hx' q
--

  -- Step 13: Calculate the length of the closed walk
  have hqLength := hq.length_eq
  have hlen : c.length = Fintype.card V := by
    simp only [c, Walk.length_cons]
    omega
--

  -- Step 14: A Hamiltonian walk is a path
  have hqPath : q.IsPath := by
    exact hq.isPath
--

  -- Step 15: Show that the closed walk is a cycle
  have hc : c.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
--
    · simp only [c, Walk.tail_cons]
--
      -- exact hqPath
      -- simpa using hqPath

      -- Need to deal with Walk.copy.
      exact (Walk.isPath_copy q _ _).2 hqPath
--
    · omega
      
--
  -- Step 16: Show that the cycle is Hamiltonian
  have hcHam : c.IsHamiltonianCycle := by
    rw [Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
    constructor
    · exact hc
    · exact hlen
      
    
  -- Step 17: Conclude that H is Hamiltonian
  -- exact hcHam
  unfold SimpleGraph.IsHamiltonian
  intro hV
  refine ⟨p.getVert j, c, ?_⟩
  exact hcHam


-- Lemma 3.2: No simultaneous cross edges
theorem no_cross_edges
    {x y : V}
    (p : H.Walk x y)
    (hp : p.IsHamiltonian)
    (hn : 3 ≤ Fintype.card V)
    (hH : ¬ H.IsHamiltonian)
    (j : ℕ)
    (hj₁ : 1 ≤ j)
    (hj₂ : j ≤ p.length) :
    ¬ (H.Adj x (p.getVert j) ∧
       H.Adj (p.getVert (j - 1)) y) := by
--
  contrapose hH
  exact cycle_construction H p hp hn j hj₁ hj₂ hH.1 hH.2

end TeamOre
