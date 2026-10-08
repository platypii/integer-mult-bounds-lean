import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Actual weighted-graph source partitions behind paired exclusion. Vertex
weights and edge weights are distinct source atoms. Groups of at most two
vertices permit reconstruction without subtraction: coarse outside values,
remaining-vertex strips, and the surviving cross edge have disjoint supports.
These are support and finite-sum identities, not circuit-size or tape bounds. -/

namespace IntegerMultBounds.Networks.PairedPartition

variable {V A : Type*} [DecidableEq V]

inductive Source (V : Type*) where
  | vertex (v : V)
  | edge (u v : V)
  deriving DecidableEq

/-- Oriented edge names distinguish source identifiers; the incidence tests
below are symmetric. A graph may choose either orientation of each edge. -/
def endpoints : Source V → Finset V
  | .vertex v => {v}
  | .edge u v => {u, v}

def Loopless (sources : Finset (Source V)) : Prop :=
  ∀ u v, Source.edge u v ∈ sources → u ≠ v

def Within (sources : Finset (Source V)) (points : Finset V) : Prop :=
  ∀ s ∈ sources, endpoints s ⊆ points

def avoiding (sources : Finset (Source V)) (excluded : Finset V) : Finset (Source V) :=
  sources.filter (fun s => Disjoint (endpoints s) excluded)

def confined (sources : Finset (Source V)) (group : Finset V) : Finset (Source V) :=
  sources.filter (fun s => endpoints s ⊆ group)

@[simp] theorem mem_avoiding (sources : Finset (Source V)) (excluded : Finset V) (s : Source V) :
    s ∈ avoiding sources excluded ↔ s ∈ sources ∧ Disjoint (endpoints s) excluded := Finset.mem_filter

@[simp] theorem mem_confined (sources : Finset (Source V)) (group : Finset V) (s : Source V) :
    s ∈ confined sources group ↔ s ∈ sources ∧ endpoints s ⊆ group := Finset.mem_filter

def vertexWeights (sources : Finset (Source V)) (group : Finset V) : Finset (Source V) :=
  sources.filter (fun s => (match s with | .vertex v => decide (v ∈ group) | .edge _ _ => false) = true)

def edgeWeights (sources : Finset (Source V)) (group : Finset V) : Finset (Source V) :=
  sources.filter (fun s => (match s with | .vertex _ => false | .edge u v => decide (u ∈ group ∧ v ∈ group)) = true)

/-- The coarse vertex weight is the original vertex weights plus internal edges. -/
def groupWeight (sources : Finset (Source V)) (group : Finset V) : Finset (Source V) :=
  vertexWeights sources group ∪ edgeWeights sources group

/-- A coarse edge is the union of original edge sources crossing its groups. -/
def bridge (sources : Finset (Source V)) (left right : Finset V) : Finset (Source V) :=
  sources.filter (fun s => (match s with
    | .vertex _ => false
    | .edge u v => decide ((u ∈ left ∧ v ∈ right) ∨ (v ∈ left ∧ u ∈ right))) = true)

/-- The strip at a removed vertex retains the other vertex's weight and its
edges to all groups except its own and the explicitly excluded other group. -/
def strip (sources : Finset (Source V)) (points group : Finset V) (removed : V)
    (excluded : Finset V) : Finset (Source V) :=
  vertexWeights sources (group.erase removed) ∪
    bridge sources (group.erase removed) ((points \ group) \ excluded)

theorem groupWeight_eq_confined (sources : Finset (Source V)) (group : Finset V) :
    groupWeight sources group = confined sources group := by
  ext s
  cases s <;> simp [groupWeight, vertexWeights, edgeWeights, mem_confined, endpoints, Finset.insert_subset_iff, Finset.singleton_subset_iff]

theorem groupWeight_disjoint (sources : Finset (Source V)) (group : Finset V) :
    Disjoint (vertexWeights sources group) (edgeWeights sources group) := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  cases s <;> simp_all [vertexWeights, edgeWeights]

/-- Two remaining distinct vertices cannot both lie in a paired group after
one specified member has been removed. -/
private theorem survivors_equal (group : Finset V) (a u v : V) (hsize : group.card ≤ 2)
    (ha : a ∈ group) (hu : u ∈ group) (hv : v ∈ group) (hua : u ≠ a) (hva : v ≠ a) : u = v := by
  have he : (group.erase a).card ≤ 1 := by
    rw [Finset.card_erase_of_mem ha]
    omega
  exact Finset.card_le_one.mp he u (by simp [hu, hua]) v (by simp [hv, hva])

/-- Coarse aggregation partitions all terms in two disjoint groups into their
internal weights and the actual crossing edge sources. -/
theorem coarse_union (sources : Finset (Source V)) (left right : Finset V) :
    confined sources (left ∪ right) = groupWeight sources left ∪ groupWeight sources right ∪ bridge sources left right := by
  ext s
  cases s <;> simp only [mem_confined, groupWeight, vertexWeights, edgeWeights, bridge, endpoints,
    Finset.mem_filter, Finset.mem_union, Finset.singleton_subset_iff, Finset.insert_subset_iff]
  all_goals aesop (config := {maxRuleApplications := 1000})

theorem coarse_disjoint (sources : Finset (Source V)) (left right : Finset V)
    (hd : Disjoint left right) :
    Disjoint (groupWeight sources left) (groupWeight sources right) ∧
    Disjoint (groupWeight sources left ∪ groupWeight sources right) (bridge sources left right) := by
  constructor <;> apply Finset.disjoint_left.mpr <;> intro s hs ht
  all_goals cases s <;> simp_all [groupWeight, vertexWeights, edgeWeights, bridge]
  all_goals have hh := Finset.disjoint_left.mp hd; aesop

/-- Single exclusion is a coarse outside term plus its remaining-vertex strip. -/
theorem single_union (sources : Finset (Source V)) (points group : Finset V) (a : V)
    (hw : Within sources points) (hl : Loopless sources)
    (hsize : group.card ≤ 2) (ha : a ∈ group) :
    avoiding sources {a} = avoiding sources group ∪ strip sources points group a ∅ := by
  ext s
  by_cases hs : s ∈ sources
  · have hp := hw s hs
    cases s with
    | vertex v =>
      simp only [endpoints, Finset.singleton_subset_iff] at hp
      simp [mem_avoiding, strip, vertexWeights, bridge, endpoints, hs]
      by_cases hv : v ∈ group <;> simp_all [eq_comm]
      aesop
    | edge u v =>
      have hne := hl u v hs
      have hn : ¬(u ∈ group ∧ v ∈ group ∧ u ≠ a ∧ v ≠ a) := by
        rintro ⟨hu, hv, hua, hva⟩
        exact hne (survivors_equal group a u v hsize ha hu hv hua hva)
      simp only [endpoints, Finset.insert_subset_iff, Finset.singleton_subset_iff] at hp
      simp [mem_avoiding, strip, vertexWeights, bridge, endpoints, hs, hp.1, hp.2]
      by_cases hu : u ∈ group <;> by_cases hv : v ∈ group <;> simp_all [eq_comm] <;> aesop
  · cases s <;> simp [mem_avoiding, strip, vertexWeights, bridge, hs]

theorem single_disjoint (sources : Finset (Source V)) (points group : Finset V) (a : V) :
    Disjoint (avoiding sources group) (strip sources points group a ∅) := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  cases s <;> simp_all [mem_avoiding, strip, vertexWeights, bridge, endpoints]

/-- Two different members exhaust a group of size at most two, so its
same-group double exclusion is exactly the coarse outside value. -/
theorem same_group (sources : Finset (Source V)) (group : Finset V) (a b : V)
    (hsize : group.card ≤ 2) (ha : a ∈ group) (hb : b ∈ group) (hne : a ≠ b) :
    avoiding sources {a, b} = avoiding sources group := by
  have hab : ({a, b} : Finset V) ⊆ group := by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, ha, hb]
  have hc : ({a, b} : Finset V).card = 2 := by simp [hne]
  have he : ({a, b} : Finset V) = group := Finset.eq_of_subset_of_card_le hab (by omega)
  rw [he]

/-- Cross-group double exclusion uses precisely the four source classes in
the script: far, left strip, right strip, and the surviving cross edges. -/
theorem pair_union (sources : Finset (Source V)) (points left right : Finset V) (a b : V)
    (hw : Within sources points) (hl : Loopless sources) (hdis : Disjoint left right)
    (hleft : left.card ≤ 2) (hright : right.card ≤ 2) (ha : a ∈ left) (hb : b ∈ right) :
    avoiding sources {a, b} =
      avoiding sources (left ∪ right) ∪ strip sources points left a right ∪
        strip sources points right b left ∪ bridge sources (left.erase a) (right.erase b) := by
  ext s
  by_cases hs : s ∈ sources
  · have hp := hw s hs
    have hnot (v : V) : ¬(v ∈ left ∧ v ∈ right) := fun hh => Finset.disjoint_left.mp hdis hh.1 hh.2
    cases s with
    | vertex v =>
      simp only [endpoints, Finset.singleton_subset_iff] at hp
      simp [mem_avoiding, strip, vertexWeights, bridge, endpoints, hs]
      by_cases hlv : v ∈ left <;> by_cases hrv : v ∈ right <;> simp_all [eq_comm] <;> aesop
    | edge u v =>
      have hne := hl u v hs
      have hnl : ¬(u ∈ left ∧ v ∈ left ∧ u ≠ a ∧ v ≠ a) := by
        rintro ⟨hu, hv, hua, hva⟩
        exact hne (survivors_equal left a u v hleft ha hu hv hua hva)
      have hnr : ¬(u ∈ right ∧ v ∈ right ∧ u ≠ b ∧ v ≠ b) := by
        rintro ⟨hu, hv, hua, hva⟩
        exact hne (survivors_equal right b u v hright hb hu hv hua hva)
      simp only [endpoints, Finset.insert_subset_iff, Finset.singleton_subset_iff] at hp
      simp [mem_avoiding, strip, vertexWeights, bridge, endpoints, hs, hp.1, hp.2]
      by_cases hlu : u ∈ left <;> by_cases hru : u ∈ right <;>
        by_cases hlv : v ∈ left <;> by_cases hrv : v ∈ right <;> simp_all [eq_comm] <;> aesop
  · cases s <;> simp [mem_avoiding, strip, vertexWeights, bridge, hs]

/-- The four reconstruction supports are pairwise disjoint, so the three
literal additions need no cancellation. -/
theorem pair_disjoint (sources : Finset (Source V)) (points left right : Finset V) (a b : V)
    (hdis : Disjoint left right) :
    Disjoint (avoiding sources (left ∪ right)) (strip sources points left a right) ∧
    Disjoint (avoiding sources (left ∪ right) ∪ strip sources points left a right)
      (strip sources points right b left) ∧
    Disjoint (avoiding sources (left ∪ right) ∪ strip sources points left a right ∪
      strip sources points right b left) (bridge sources (left.erase a) (right.erase b)) := by
  have hnot (v : V) : ¬(v ∈ left ∧ v ∈ right) := fun hh => Finset.disjoint_left.mp hdis hh.1 hh.2
  refine ⟨?_, ?_, ?_⟩ <;> apply Finset.disjoint_left.mpr <;> intro s hs ht
  all_goals cases s <;> simp_all [mem_avoiding, strip, vertexWeights, bridge, endpoints]
  all_goals aesop (config := {maxRuleApplications := 1000})

/-- Aggregating outgoing edges across disjoint groups uses ordinary unions of
actual source sets, so these identities can be iterated over the group list. -/
theorem bridge_right_union (sources : Finset (Source V)) (left right next : Finset V) :
    bridge sources left (right ∪ next) = bridge sources left right ∪ bridge sources left next := by
  ext s
  cases s <;> simp [bridge]
  aesop

theorem bridge_right_disjoint (sources : Finset (Source V)) (left right next : Finset V)
    (hlr : Disjoint left right) (hln : Disjoint left next) (hrn : Disjoint right next) :
    Disjoint (bridge sources left right) (bridge sources left next) := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  have h1 := Finset.disjoint_left.mp hlr
  have h2 := Finset.disjoint_left.mp hln
  have h3 := Finset.disjoint_left.mp hrn
  cases s <;> simp_all [bridge]
  aesop

/-- The strip's carry (remaining vertex weights) and outgoing edge sources
are disjoint, exactly as required by its first total/vector construction. -/
theorem strip_disjoint (sources : Finset (Source V)) (points group : Finset V) (a : V)
    (excluded : Finset V) :
    Disjoint (vertexWeights sources (group.erase a))
      (bridge sources (group.erase a) ((points \ group) \ excluded)) := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  cases s <;> simp_all [vertexWeights, bridge]

/-- Disjointness in the script's exact three-addition grouping: first far
plus left strip, then right strip plus cross, then the two partial results. -/
theorem pair_script_disjoint (sources : Finset (Source V)) (points left right : Finset V) (a b : V)
    (hdis : Disjoint left right) :
    Disjoint (avoiding sources (left ∪ right)) (strip sources points left a right) ∧
    Disjoint (strip sources points right b left) (bridge sources (left.erase a) (right.erase b)) ∧
    Disjoint (avoiding sources (left ∪ right) ∪ strip sources points left a right)
      (strip sources points right b left ∪ bridge sources (left.erase a) (right.erase b)) := by
  obtain ⟨h1, h2, h3⟩ := pair_disjoint sources points left right a b hdis
  obtain ⟨hfar, hstrip⟩ := Finset.disjoint_union_left.mp h3
  exact ⟨h1, hstrip, Finset.disjoint_union_right.mpr ⟨h2, hfar⟩⟩

section Sums

variable [AddCommMonoid A]

def value (weight : Source V → A) (support : Finset (Source V)) : A := ∑ s ∈ support, weight s

theorem coarse_value (weight : Source V → A) (sources : Finset (Source V)) (left right : Finset V)
    (hd : Disjoint left right) :
    value weight (confined sources (left ∪ right)) =
      value weight (groupWeight sources left) + value weight (groupWeight sources right) +
        value weight (bridge sources left right) := by
  rw [coarse_union]
  obtain ⟨h1, h2⟩ := coarse_disjoint sources left right hd
  exact (Finset.sum_union h2).trans (congrArg (fun x => x + value weight (bridge sources left right)) (Finset.sum_union h1))

theorem single_value (weight : Source V → A) (sources : Finset (Source V)) (points group : Finset V) (a : V)
    (hw : Within sources points) (hl : Loopless sources) (hsize : group.card ≤ 2) (ha : a ∈ group) :
    value weight (avoiding sources {a}) = value weight (avoiding sources group) +
      value weight (strip sources points group a ∅) := by
  rw [single_union sources points group a hw hl hsize ha]
  exact Finset.sum_union (single_disjoint sources points group a)

theorem pair_value (weight : Source V → A) (sources : Finset (Source V)) (points left right : Finset V) (a b : V)
    (hw : Within sources points) (hl : Loopless sources) (hdis : Disjoint left right)
    (hleft : left.card ≤ 2) (hright : right.card ≤ 2) (ha : a ∈ left) (hb : b ∈ right) :
    value weight (avoiding sources {a, b}) = value weight (avoiding sources (left ∪ right)) +
      value weight (strip sources points left a right) + value weight (strip sources points right b left) +
        value weight (bridge sources (left.erase a) (right.erase b)) := by
  rw [pair_union sources points left right a b hw hl hdis hleft hright ha hb]
  obtain ⟨h1, h2, h3⟩ := pair_disjoint sources points left right a b hdis
  simp only [value, Finset.sum_union h1, Finset.sum_union h2, Finset.sum_union h3]

/-- The cross-pair value identity with the parenthesization executed upstream. -/
theorem pair_script_value (weight : Source V → A) (sources : Finset (Source V))
    (points left right : Finset V) (a b : V)
    (hw : Within sources points) (hl : Loopless sources) (hdis : Disjoint left right)
    (hleft : left.card ≤ 2) (hright : right.card ≤ 2) (ha : a ∈ left) (hb : b ∈ right) :
    value weight (avoiding sources {a, b}) =
      (value weight (avoiding sources (left ∪ right)) + value weight (strip sources points left a right)) +
      (value weight (strip sources points right b left) + value weight (bridge sources (left.erase a) (right.erase b))) := by
  rw [pair_value weight sources points left right a b hw hl hdis hleft hright ha hb, add_assoc]

end Sums

end IntegerMultBounds.Networks.PairedPartition
