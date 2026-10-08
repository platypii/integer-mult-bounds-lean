import IntegerMultBounds.Networks.MaskDAG
import IntegerMultBounds.Networks.PairedInitialGraph
import Mathlib.Data.List.NodupEquivFin

/-! Canonical bit positions and exclusion masks for the literal pair-input
order. The masks retain the exact sorted combinations used by the circuit. -/

namespace IntegerMultBounds.Networks.PairMask

open PairedCircuit MaskDAG

@[simp] theorem pairs_range_length (n : ℕ) : (pairs (List.range n)).length = n.choose 2 := by
  rw [PairedInitialGraph.pairs_length, List.length_range]

/-- Decode a source bit position in the upstream combinations order. -/
def pairAt (n : ℕ) (i : Fin (n.choose 2)) : ℕ × ℕ :=
  (pairs (List.range n))[i.val]'(by rw [pairs_range_length]; exact i.isLt)

theorem pairAt_mem (n : ℕ) (i : Fin (n.choose 2)) : pairAt n i ∈ pairs (List.range n) :=
  List.getElem_mem _

/-- The source-index equivalence includes exactly the actual pair inputs. -/
def pairEquiv (n : ℕ) : Fin (n.choose 2) ≃ {p // p ∈ pairs (List.range n)} :=
  (finCongr (pairs_range_length n).symm).trans
    (List.Nodup.getEquiv _ (PairedCircuitCorrect.pairs_nodup _ List.pairwise_lt_range))

@[simp] theorem pairEquiv_val (n : ℕ) (i : Fin (n.choose 2)) : (pairEquiv n i).val = pairAt n i := rfl

theorem pairAt_injective (n : ℕ) : Function.Injective (pairAt n) := by
  intro i j he
  apply (pairEquiv n).injective
  exact Subtype.ext he

/-- A singleton bit at an arbitrary natural index; out-of-range bits vanish. -/
def bit (width i : ℕ) : BitVec width := BitVec.ofNat width 1 <<< i

theorem mem_bit (width i : ℕ) (j : Fin width) : j ∈ decode (bit width i) ↔ j.val = i := by
  simp only [mem_decode, bit, BitVec.getLsbD_shiftLeft]
  rw [BitVec.getLsbD_one]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  have hj := j.isLt
  omega

/-- OR only the listed singleton bits, without scanning all source positions. -/
def maskOfIndices (width : ℕ) : List ℕ → BitVec width
  | [] => 0
  | i :: indices => bit width i ||| maskOfIndices width indices

@[simp] theorem mem_maskOfIndices (width : ℕ) (indices : List ℕ) (i : Fin width) :
    i ∈ decode (maskOfIndices width indices) ↔ i.val ∈ indices := by
  induction indices with
  | nil => simp [maskOfIndices]
  | cons j indices ih =>
    rw [maskOfIndices, decode_or, Finset.mem_union, mem_bit, ih, List.mem_cons]

/-- A single linear pass selects the source indices incident to a vertex. -/
def incidentIndices (n a : ℕ) : List ℕ :=
  ((pairs (List.range n)).zipIdx.filter (fun e => e.1.1 = a ∨ e.1.2 = a)).map Prod.snd

/-- Only n-1 nonzero singleton masks enter each incident mask. -/
def incident (n a : ℕ) : BitVec (n.choose 2) := maskOfIndices (n.choose 2) (incidentIndices n a)

theorem mem_incident (n a : ℕ) (i : Fin (n.choose 2)) :
    i ∈ decode (incident n a) ↔ (pairAt n i).1 = a ∨ (pairAt n i).2 = a := by
  rw [incident, mem_maskOfIndices]
  simp only [incidentIndices, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨p, j⟩, ⟨hp, ha⟩, hj⟩
    change j = i.val at hj
    subst j
    have he := List.mk_mem_zipIdx_iff_getElem?.mp hp
    have hi : i.val < (pairs (List.range n)).length := by rw [pairs_range_length]; exact i.isLt
    rw [List.getElem?_eq_getElem hi] at he
    have he' : pairAt n i = p := Option.some.inj he
    simpa [he'] using ha
  · intro ha
    refine ⟨(pairAt n i, i.val), ⟨?_, ha⟩, rfl⟩
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    exact List.getElem?_eq_getElem (by rw [pairs_range_length]; exact i.isLt)

/-- The finite-width complement leaves precisely sources avoiding both vertices. -/
def exclusion (n a b : ℕ) : BitVec (n.choose 2) := ~~~incident n a &&& ~~~incident n b

theorem mem_exclusion (n a b : ℕ) (i : Fin (n.choose 2)) :
    i ∈ decode (exclusion n a b) ↔
      (pairAt n i).1 ∉ [a,b] ∧ (pairAt n i).2 ∉ [a,b] := by
  have ha := mem_incident n a i
  have hb := mem_incident n b i
  simp only [mem_decode] at ha hb ⊢
  simp only [exclusion, BitVec.getLsbD_and, BitVec.getLsbD_not, Bool.and_eq_true,
    Bool.not_eq_true', List.mem_cons]
  cases hba : (incident n a).getLsbD i.val <;> cases hbb : (incident n b).getLsbD i.val <;>
    simp_all <;> tauto

/-- Exclusion masks interpreted as actual pair keys give the same query support
as the unweighted paired algorithm. -/
theorem exclusion_image (n a b : ℕ) :
    (decode (exclusion n a b)).image (pairAt n) =
      (pairs (List.range n)).toFinset.filter (fun p => p.1 ∉ [a,b] ∧ p.2 ∉ [a,b]) := by
  ext p
  simp only [Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨pairAt_mem n i, (mem_exclusion n a b i).mp hi⟩
  · rintro ⟨hp, ha⟩
    obtain ⟨i, hi⟩ := (pairEquiv n).surjective ⟨p, hp⟩
    have he : pairAt n i = p := congrArg Subtype.val hi
    exact ⟨i, (mem_exclusion n a b i).mpr (by simpa [he] using ha), he⟩

/-- Bit-indexed evaluation transports to the literal pair-input sum. -/
theorem exclusion_sum {A : Type*} [AddCommMonoid A] (input : ℕ × ℕ → A) (n a b : ℕ) :
    DisjointCircuit.supportSum (fun i => input (pairAt n i)) (decode (exclusion n a b)) =
      DisjointCircuit.supportSum input
        ((pairs (List.range n)).toFinset.filter (fun p => p.1 ∉ [a,b] ∧ p.2 ∉ [a,b])) := by
  rw [← exclusion_image]
  unfold DisjointCircuit.supportSum
  exact (Finset.sum_image (fun i _ j _ he => pairAt_injective n he)).symm

/-- The h=50 local certificate has exactly 1176 source bits. -/
abbrev incident49 (a : ℕ) : BitVec 1176 := incident 49 a
abbrev exclusion49 (a b : ℕ) : BitVec 1176 := exclusion 49 a b
abbrev pairAt49 : Fin 1176 → ℕ × ℕ := pairAt 49

end IntegerMultBounds.Networks.PairMask
