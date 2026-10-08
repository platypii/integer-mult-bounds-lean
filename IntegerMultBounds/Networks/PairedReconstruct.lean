import IntegerMultBounds.Networks.PairedPartition
import IntegerMultBounds.Networks.DisjointBuilder

/-! Literal local reconstruction steps of the paired-exclusion DAG builder.
The source supports are the concrete weighted-graph partitions, and every
addition uses the existing zero-eliding, support-interning smart constructor.
This proves one recursive reconstruction step, not the full recursive graph
builder or its optimized global node count. -/

namespace IntegerMultBounds.Networks.PairedReconstruct

open DisjointCircuit DisjointBuilder PairedPartition

variable {V A : Type*} [DecidableEq V]

/-- Exact upstream order: far plus left strip, right strip plus cross, then
combine the two partial results. Each step sees the physically extended DAG. -/
def pair (nodes : List (Node (Source V))) (far leftStrip rightStrip cross : Ref) : Result (Source V) :=
  let left := smartAdd nodes far leftStrip
  let right := smartAdd left.1 rightStrip cross
  smartAdd right.1 left.2 right.2

/-- One actual smart addition reconstructs a single exclusion. -/
def single (nodes : List (Node (Source V))) (outside remaining : Ref) : Result (Source V) :=
  smartAdd nodes outside remaining

/-- The reconstructed pair exclusion is an actual valid DAG extension with
at most three new nodes and exactly the required remaining weighted sources. -/
theorem pair_built (nodes : List (Node (Source V))) (far leftStrip rightStrip cross : Ref)
    (sources : Finset (Source V)) (points left right : Finset V) (a b : V)
    (hv : Valid nodes)
    (hf : RefValid nodes far) (hl : RefValid nodes leftStrip)
    (hr : RefValid nodes rightStrip) (hc : RefValid nodes cross)
    (hsf : refSupport nodes far = avoiding sources (left ∪ right))
    (hsl : refSupport nodes leftStrip = strip sources points left a right)
    (hsr : refSupport nodes rightStrip = strip sources points right b left)
    (hsc : refSupport nodes cross = bridge sources (left.erase a) (right.erase b))
    (hw : Within sources points) (hloop : Loopless sources) (hdis : Disjoint left right)
    (hleft : left.card ≤ 2) (hright : right.card ≤ 2) (ha : a ∈ left) (hb : b ∈ right) :
    Built nodes (pair nodes far leftStrip rightStrip cross) (avoiding sources {a, b}) 3 := by
  obtain ⟨hd1, hd2, hd3⟩ := pair_script_disjoint sources points left right a b hdis
  let first := smartAdd nodes far leftStrip
  have hfirst : Built nodes first
      (avoiding sources (left ∪ right) ∪ strip sources points left a right) 1 := by
    have hd : Disjoint (refSupport nodes far) (refSupport nodes leftStrip) := by
      rwa [hsf, hsl]
    simpa only [first, hsf, hsl] using smartAdd_built nodes far leftStrip hv hf hl hd
  let second := smartAdd first.1 rightStrip cross
  have hsecond : Built first.1 second
      (strip sources points right b left ∪ bridge sources (left.erase a) (right.erase b)) 1 := by
    have hrs : refSupport first.1 rightStrip = strip sources points right b left :=
      (refSupport_extends hfirst.extension hr).trans hsr
    have hcs : refSupport first.1 cross = bridge sources (left.erase a) (right.erase b) :=
      (refSupport_extends hfirst.extension hc).trans hsc
    have hd : Disjoint (refSupport first.1 rightStrip) (refSupport first.1 cross) := by
      rwa [hrs, hcs]
    simpa only [second, hrs, hcs] using smartAdd_built first.1 rightStrip cross hfirst.valid
      (refValid_extends hfirst.extension hr) (refValid_extends hfirst.extension hc) hd
  have hls : refSupport second.1 first.2 =
      avoiding sources (left ∪ right) ∪ strip sources points left a right :=
    (refSupport_extends hsecond.extension hfirst.refValid).trans hfirst.support_eq
  have hd : Disjoint (refSupport second.1 first.2) (refSupport second.1 second.2) := by
    rwa [hls, hsecond.support_eq]
  have hfinal := smartAdd_built second.1 first.2 second.2 hsecond.valid
    (refValid_extends hsecond.extension hfirst.refValid) hsecond.refValid hd
  refine ⟨hfinal.valid, extends_trans hfirst.extension (extends_trans hsecond.extension hfinal.extension),
    hfinal.refValid, ?_, ?_⟩
  · change refSupport (smartAdd second.1 first.2 second.2).1 (smartAdd second.1 first.2 second.2).2 = _
    rw [hfinal.support_eq, hls, hsecond.support_eq,
      pair_union sources points left right a b hw hloop hdis hleft hright ha hb]
    simp only [Finset.union_assoc]
  · have h1 := hfirst.length_le
    have h2 := hsecond.length_le
    have h3 := hfinal.length_le
    change (smartAdd second.1 first.2 second.2).1.length ≤ _
    omega

/-- Outside plus the actual remaining-vertex strip gives the complete single
exclusion, using at most one newly appended node. -/
theorem single_built (nodes : List (Node (Source V))) (outside remaining : Ref)
    (sources : Finset (Source V)) (points group : Finset V) (a : V) (hv : Valid nodes)
    (ho : RefValid nodes outside) (hr : RefValid nodes remaining)
    (hso : refSupport nodes outside = avoiding sources group)
    (hsr : refSupport nodes remaining = strip sources points group a ∅)
    (hw : Within sources points) (hloop : Loopless sources) (hsize : group.card ≤ 2) (ha : a ∈ group) :
    Built nodes (single nodes outside remaining) (avoiding sources {a}) 1 := by
  have hd : Disjoint (refSupport nodes outside) (refSupport nodes remaining) := by
    rw [hso, hsr]
    exact single_disjoint sources points group a
  have hh := smartAdd_built nodes outside remaining hv ho hr hd
  simpa only [single, hso, hsr, ← single_union sources points group a hw hloop hsize ha] using hh

section Semantics

variable [AddCommMonoid A]

/-- The three actual additions return the sum of precisely the edge and vertex
weights avoiding the excluded pair. -/
theorem pair_value (input : Source V → A) (nodes : List (Node (Source V)))
    (far leftStrip rightStrip cross : Ref)
    (sources : Finset (Source V)) (points left right : Finset V) (a b : V)
    (hv : Valid nodes) (hf : RefValid nodes far) (hl : RefValid nodes leftStrip)
    (hr : RefValid nodes rightStrip) (hc : RefValid nodes cross)
    (hsf : refSupport nodes far = avoiding sources (left ∪ right))
    (hsl : refSupport nodes leftStrip = strip sources points left a right)
    (hsr : refSupport nodes rightStrip = strip sources points right b left)
    (hsc : refSupport nodes cross = bridge sources (left.erase a) (right.erase b))
    (hw : Within sources points) (hloop : Loopless sources) (hdis : Disjoint left right)
    (hleft : left.card ≤ 2) (hright : right.card ≤ 2) (ha : a ∈ left) (hb : b ∈ right) :
    refValue input (pair nodes far leftStrip rightStrip cross).1 (pair nodes far leftStrip rightStrip cross).2 =
      ∑ s ∈ avoiding sources {a, b}, input s := by
  have hh := pair_built nodes far leftStrip rightStrip cross sources points left right a b hv hf hl hr hc
    hsf hsl hsr hsc hw hloop hdis hleft hright ha hb
  rw [refValue_eq input _ _ hh.valid hh.refValid, hh.support_eq]
  rfl

/-- Every old node reference, including spectators and all four operands,
retains its computed value through the three-addition reconstruction. -/
theorem pair_preserves (input : Source V → A) (nodes : List (Node (Source V)))
    (far leftStrip rightStrip cross old : Ref)
    (sources : Finset (Source V)) (points left right : Finset V) (a b : V)
    (hv : Valid nodes) (hf : RefValid nodes far) (hl : RefValid nodes leftStrip)
    (hr : RefValid nodes rightStrip) (hc : RefValid nodes cross) (ho : RefValid nodes old)
    (hsf : refSupport nodes far = avoiding sources (left ∪ right))
    (hsl : refSupport nodes leftStrip = strip sources points left a right)
    (hsr : refSupport nodes rightStrip = strip sources points right b left)
    (hsc : refSupport nodes cross = bridge sources (left.erase a) (right.erase b))
    (hw : Within sources points) (hloop : Loopless sources) (hdis : Disjoint left right)
    (hleft : left.card ≤ 2) (hright : right.card ≤ 2) (ha : a ∈ left) (hb : b ∈ right) :
    refValue input (pair nodes far leftStrip rightStrip cross).1 old = refValue input nodes old := by
  have hh := pair_built nodes far leftStrip rightStrip cross sources points left right a b hv hf hl hr hc
    hsf hsl hsr hsc hw hloop hdis hleft hright ha hb
  exact refValue_extends input hh.extension hv hh.valid ho

theorem single_value (input : Source V → A) (nodes : List (Node (Source V))) (outside remaining : Ref)
    (sources : Finset (Source V)) (points group : Finset V) (a : V) (hv : Valid nodes)
    (ho : RefValid nodes outside) (hr : RefValid nodes remaining)
    (hso : refSupport nodes outside = avoiding sources group)
    (hsr : refSupport nodes remaining = strip sources points group a ∅)
    (hw : Within sources points) (hloop : Loopless sources) (hsize : group.card ≤ 2) (ha : a ∈ group) :
    refValue input (single nodes outside remaining).1 (single nodes outside remaining).2 =
      ∑ s ∈ avoiding sources {a}, input s := by
  have hh := single_built nodes outside remaining sources points group a hv ho hr hso hsr hw hloop hsize ha
  rw [refValue_eq input _ _ hh.valid hh.refValid, hh.support_eq]
  rfl

theorem single_preserves (input : Source V → A) (nodes : List (Node (Source V)))
    (outside remaining old : Ref) (sources : Finset (Source V)) (points group : Finset V) (a : V)
    (hv : Valid nodes) (ho : RefValid nodes outside) (hr : RefValid nodes remaining) (hold : RefValid nodes old)
    (hso : refSupport nodes outside = avoiding sources group)
    (hsr : refSupport nodes remaining = strip sources points group a ∅)
    (hw : Within sources points) (hloop : Loopless sources) (hsize : group.card ≤ 2) (ha : a ∈ group) :
    refValue input (single nodes outside remaining).1 old = refValue input nodes old := by
  have hh := single_built nodes outside remaining sources points group a hv ho hr hso hsr hw hloop hsize ha
  exact refValue_extends input hh.extension hv hh.valid hold

end Semantics

end IntegerMultBounds.Networks.PairedReconstruct
