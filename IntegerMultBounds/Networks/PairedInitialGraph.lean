import IntegerMultBounds.Networks.PairedQuerySupport
import IntegerMultBounds.Networks.PairedBlockCorrect

/-! Literal initial unweighted pair graph: one singleton input node per pair
in combination order, indexed references to those nodes, and absent vertex
weights. The initial graph is verified directly, without a supplied checker. -/

namespace IntegerMultBounds.Networks.PairedInitialGraph

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect
open PairedPartition PairedCoarseCorrect SupportInterpretation

abbrev Input := ℕ × ℕ

/-- The actual source node order is the upstream pair enumeration. -/
def nodes (points : List ℕ) : List (Node Input) :=
  (pairs points).map (fun p => ⟨.input p, {p}⟩)

/-- Pair key `p` points to the zero-based index of its singleton input node. -/
def edges (points : List ℕ) : EdgeTable :=
  (pairs points).zipIdx.map (fun p => (p.1, some p.2))

def weights (points : List ℕ) : WeightTable := points.map (·, none)

/-- Full executable local paired circuit, starting from its concrete inputs. -/
def circuit (points : List ℕ) : BlockResult Input :=
  block (nodes points) points (edges points) (weights points)

/-- The input payload represented by each weighted graph atom. -/
def inputSupport : Source ℕ → Finset Input
  | .vertex _ => ∅
  | .edge u v => {(u,v)}

@[simp] theorem nodes_length (points : List ℕ) : (nodes points).length = (pairs points).length := by
  simp [nodes]

private theorem inputNodes_valid (xs : List Input) (prior : List (Finset Input)) :
    ValidFrom prior (xs.map (fun p => (⟨.input p, {p}⟩ : Node Input))) := by
  induction xs generalizing prior with
  | nil => trivial
  | cons p ps ih => exact ⟨rfl, ih _⟩

theorem nodes_valid (points : List ℕ) : Valid (nodes points) := inputNodes_valid _ []

/-- Every literal indexed source reference has its exact singleton support. -/
theorem input_refSpec (points : List ℕ) (i : ℕ) (hi : i < (pairs points).length) :
    RefSpec {(pairs points)[i]} (nodes points) (some i) := by
  have hn : i < (nodes points).length := by simpa using hi
  refine ⟨hn, ?_⟩
  rw [refSupport_some _ i hn]
  simp [nodes]

theorem edges_spec (points : List ℕ) :
    TableSpec (fun p : Input => {p}) (pairs points) (nodes points) (edges points) := by
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp [edges], ?_⟩
  intro i hi hj
  simp only [List.get_eq_getElem, edges, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  exact ⟨trivial, input_refSpec points i hi⟩

theorem weights_spec (points : List ℕ) :
    TableSpec (fun _ : ℕ => (∅ : Finset Input)) points (nodes points) (weights points) := by
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp [weights], ?_⟩
  intro i hi hj
  simp only [List.get_eq_getElem, weights, List.getElem_map]
  exact ⟨trivial, trivial, rfl⟩

/-- Sorted distinct vertices produce a fully valid canonical recursive graph
with disjoint singleton edge payloads and genuinely empty vertex weights. -/
theorem graphReady (points : List ℕ) (hs : points.Pairwise (· < ·)) :
    GraphReady (nodes points) points (edges points) (weights points) := by
  apply graphReady_of_atomTable _ _ _ _ inputSupport (nodes_valid points) hs
    (edges_spec points) (weights_spec points)
  intro a _ b _ hne
  cases a <;> cases b <;> simp only [inputSupport, Finset.disjoint_empty_left, Finset.disjoint_empty_right]
  rename_i u v u' v'
  apply Finset.disjoint_singleton.mpr
  intro he
  exact hne (by cases he; rfl)

/-- The actual initial atom lookup realizes the prescribed singleton-or-zero
payload; this lemma is derived from the literal indexed tables. -/
theorem atomRef_spec (points : List ℕ) (a : Source ℕ) (ha : a ∈ atomKeys points) :
    RefSpec (inputSupport a) (nodes points) (atomRef (edges points) (weights points) a) := by
  have ht := tableSpec_atomTable inputSupport points (nodes points) (edges points) (weights points)
    (edges_spec points) (weights_spec points)
  exact tableSpec_lookup _ _ _ _ ht a ha

/-- Every omission query contains precisely the surviving original pair
inputs, with no duplicate or hidden weighted source contributions. -/
theorem query_support (points : List ℕ) (hs : points.Pairwise (· < ·)) (excluded : List ℕ) :
    supports (nodes points) (query (edges points) (weights points) excluded) =
      (pairs points).toFinset.filter (fun p => p.1 ∉ excluded ∧ p.2 ∉ excluded) := by
  rw [PairedQuerySupport.query_support (graphReady points hs)]
  have he : interpret (atomSupport (nodes points) (edges points) (weights points))
      (avoiding (atomKeys points).toFinset excluded.toFinset) =
      interpret inputSupport (avoiding (atomKeys points).toFinset excluded.toFinset) := by
    apply congr_weights
    intro a ha
    exact (atomRef_spec points a (List.mem_toFinset.mp ((mem_avoiding _ _ _).mp ha).1)).2
  rw [he]
  ext p
  simp only [mem_interpret, mem_avoiding, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨a, ⟨ha, hd⟩, hp⟩
    cases a with
    | vertex v => simp [inputSupport] at hp
    | edge u v =>
      have hp' : p = (u,v) := Finset.mem_singleton.mp hp
      subst p
      exact ⟨(edge_mem_atomKeys points u v).mp ha, by
        simpa [endpoints, Finset.disjoint_insert_left, Finset.disjoint_singleton_left] using hd⟩
  · rintro ⟨hp, hd⟩
    refine ⟨.edge p.1 p.2, ⟨(edge_mem_atomKeys points p.1 p.2).mpr hp, ?_⟩, ?_⟩
    · simpa [endpoints, Finset.disjoint_insert_left, Finset.disjoint_singleton_left] using hd
    · exact Finset.mem_singleton.mpr (Prod.eta p).symm

/-- Analytic pair count for the literal recursive combination enumeration. -/
theorem pairs_length (points : List ℕ) : (pairs points).length = points.length.choose 2 := by
  induction points with
  | nil => rfl
  | cons a ps ih => simp [pairs, ih, Nat.choose_succ_succ]

theorem input_count (points : List ℕ) : (nodes points).length = points.length.choose 2 := by
  rw [nodes_length, pairs_length]

/-- The shared-point h=50 application has 49 remaining vertices and 1176 pair inputs. -/
theorem input_count_49 : (nodes (List.range 49)).length = 1176 := by
  rw [input_count, List.length_range]
  norm_num [Nat.choose_two_right]

/-- End-to-end support correctness of the actual unweighted local generator:
its initial graph hypotheses are all discharged by the concrete construction. -/
theorem circuit_correct (points : List ℕ) (hs : points.Pairwise (· < ·)) :
    BlockCorrect (nodes points) points (edges points) (weights points) (circuit points) :=
  PairedBlockCorrect.block_correct _ _ _ _ (graphReady points hs)

/-- Each actual local output contains exactly the original pair inputs that
avoid its two excluded vertices. -/
theorem circuit_pair_support (points : List ℕ) (hs : points.Pairwise (· < ·))
    (p : Input) (hp : p ∈ pairs points) :
    RefSpec ((pairs points).toFinset.filter (fun q =>
      q.1 ∉ [p.1, p.2] ∧ q.2 ∉ [p.1, p.2]))
      (circuit points).nodes (lookup (circuit points).two p) := by
  have hh := (circuit_correct points hs).two p hp
  rwa [query_support points hs] at hh

theorem circuit_total_support (points : List ℕ) (hs : points.Pairwise (· < ·)) :
    RefSpec (pairs points).toFinset (circuit points).nodes (circuit points).total := by
  have hh := (circuit_correct points hs).total
  rw [query_support points hs] at hh
  simpa using hh

/-- The concrete local outputs evaluate to the surviving pair-input sum over
any additive commutative monoid; no cancellation or sampled check is used. -/
theorem circuit_pair_value {A : Type*} [AddCommMonoid A] (input : Input → A)
    (points : List ℕ) (hs : points.Pairwise (· < ·)) (p : Input) (hp : p ∈ pairs points) :
    refValue input (circuit points).nodes (lookup (circuit points).two p) =
      supportSum input ((pairs points).toFinset.filter (fun q =>
        q.1 ∉ [p.1, p.2] ∧ q.2 ∉ [p.1, p.2])) := by
  have hh := circuit_pair_support points hs p hp
  rw [refValue_eq input _ _ (circuit_correct points hs).valid hh.1, hh.2]

/-- Unconditional correctness of the actual 49-vertex local paired circuit
used at h=50: all graph premises have been proved for its concrete inputs. -/
theorem circuit49_correct :
    BlockCorrect (nodes (List.range 49)) (List.range 49) (edges (List.range 49))
      (weights (List.range 49)) (circuit (List.range 49)) :=
  circuit_correct _ List.pairwise_lt_range

theorem circuit49_valid : Valid (circuit (List.range 49)).nodes := circuit49_correct.valid

/-- There is exactly one actual keyed output per excluded pair. This counts
outputs only; it makes no claim about active addition or scratch counts. -/
theorem circuit49_output_count : (circuit (List.range 49)).two.length = 1176 := by
  have hh := circuit49_correct.two_keys.length_eq
  have he : Nat.choose 49 2 = 1176 := by norm_num [Nat.choose_two_right]
  simpa only [List.length_map, pairs_length, List.length_range, he] using hh

end IntegerMultBounds.Networks.PairedInitialGraph
