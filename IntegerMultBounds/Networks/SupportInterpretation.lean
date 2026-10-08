import IntegerMultBounds.Networks.DisjointCircuit

/-! Interpret weighted graph atoms as disjoint supports of original inputs.
This transports source partitions through coarse graph aggregation, where
one vertex or edge weight already represents many original sources. -/

namespace IntegerMultBounds.Networks.SupportInterpretation

variable {α β A : Type*} [DecidableEq α] [DecidableEq β]

/-- Expand a set of weighted atoms into its actual original input support. -/
def interpret (weight : α → Finset β) (atoms : Finset α) : Finset β := atoms.biUnion weight

/-- Distinct active atoms carry disjoint original input supports. Empty weights
are permitted, as required by the initial zero vertex weights. -/
def DisjointOn (weight : α → Finset β) (domain : Finset α) : Prop :=
  (↑domain : Set α).PairwiseDisjoint weight

omit [DecidableEq α] in
@[simp] theorem mem_interpret (weight : α → Finset β) (atoms : Finset α) (b : β) :
    b ∈ interpret weight atoms ↔ ∃ a ∈ atoms, b ∈ weight a := Finset.mem_biUnion

omit [DecidableEq α] in
@[simp] theorem interpret_empty (weight : α → Finset β) : interpret weight ∅ = ∅ := by
  simp [interpret]

omit [DecidableEq α] in
@[simp] theorem interpret_singleton (weight : α → Finset β) (a : α) :
    interpret weight {a} = weight a := by simp [interpret]

@[simp] theorem interpret_union (weight : α → Finset β) (s t : Finset α) :
    interpret weight (s ∪ t) = interpret weight s ∪ interpret weight t := by
  ext b
  simp only [mem_interpret, Finset.mem_union]
  aesop

@[simp] theorem interpret_insert (weight : α → Finset β) (a : α) (s : Finset α) :
    interpret weight (insert a s) = weight a ∪ interpret weight s := by
  rw [← Finset.singleton_union, interpret_union, interpret_singleton]

omit [DecidableEq α] in
theorem monotone (weight : α → Finset β) : Monotone (interpret weight) := by
  intro s t hst b hb
  obtain ⟨a, ha, hb⟩ := mem_interpret weight s b |>.mp hb
  exact (mem_interpret weight t b).mpr ⟨a, hst ha, hb⟩

omit [DecidableEq α] in
theorem congr_weights (f g : α → Finset β) (atoms : Finset α)
    (he : ∀ a ∈ atoms, f a = g a) : interpret f atoms = interpret g atoms := by
  exact Finset.biUnion_congr rfl he

omit [DecidableEq α] [DecidableEq β] in
theorem DisjointOn.mono {weight : α → Finset β} {domain part : Finset α}
    (h : DisjointOn weight domain) (hp : part ⊆ domain) : DisjointOn weight part := by
  intro a ha b hb hne
  exact h (hp ha) (hp hb) hne

omit [DecidableEq α] in
/-- A genuine partition of weighted atoms remains disjoint after expansion. -/
theorem disjoint_interpret (weight : α → Finset β) (domain s t : Finset α)
    (hw : DisjointOn weight domain) (hs : s ⊆ domain) (ht : t ⊆ domain)
    (hd : Disjoint s t) : Disjoint (interpret weight s) (interpret weight t) := by
  apply Finset.disjoint_left.mpr
  intro x hxs hxt
  obtain ⟨a, ha, hxa⟩ := (mem_interpret _ _ _).mp hxs
  obtain ⟨b, hb, hxb⟩ := (mem_interpret _ _ _).mp hxt
  have hab : a ≠ b := by
    rintro rfl
    exact Finset.disjoint_left.mp hd ha hb
  exact Finset.disjoint_left.mp (hw (hs ha) (ht hb) hab) hxa hxb

omit [DecidableEq α] in
/-- Coarse weights formed from disjoint atom blocks satisfy the same invariant. -/
theorem disjointOn_blocks {γ : Type*} [DecidableEq γ]
    (weight : α → Finset β) (domain : Finset α) (blocks : γ → Finset α) (active : Finset γ)
    (hw : DisjointOn weight domain)
    (hblocks : DisjointOn blocks active) (hsub : ∀ i ∈ active, blocks i ⊆ domain) :
    DisjointOn (fun i => interpret weight (blocks i)) active := by
  intro i hi j hj hij
  exact disjoint_interpret weight domain (blocks i) (blocks j) hw (hsub i hi) (hsub j hj)
    (hblocks hi hj hij)

omit [DecidableEq α] in
/-- Empty atom weights need not be injective; with nonempty weights, the
interpretation also reflects disjointness exactly. -/
theorem disjoint_iff (weight : α → Finset β) (domain s t : Finset α)
    (hw : DisjointOn weight domain) (hs : s ⊆ domain) (ht : t ⊆ domain)
    (hne : ∀ a ∈ domain, (weight a).Nonempty) :
    Disjoint (interpret weight s) (interpret weight t) ↔ Disjoint s t := by
  constructor
  · intro hd
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨b, hba⟩ := hne a (hs ha)
    exact Finset.disjoint_left.mp hd ((mem_interpret _ _ _).mpr ⟨a, ha, hba⟩)
      ((mem_interpret _ _ _).mpr ⟨a, hb, hba⟩)
  · exact disjoint_interpret weight domain s t hw hs ht

section Values
variable [AddCommMonoid A]

omit [DecidableEq α] in
/-- Actual weighted sums are preserved by disjoint support interpretation. -/
theorem sum_interpret (weight : α → Finset β) (domain atoms : Finset α)
    (hw : DisjointOn weight domain) (hs : atoms ⊆ domain) (input : β → A) :
    (∑ b ∈ interpret weight atoms, input b) = ∑ a ∈ atoms, ∑ b ∈ weight a, input b := by
  exact Finset.sum_biUnion (hw.mono hs)

omit [DecidableEq α] in
theorem supportSum_interpret (weight : α → Finset β) (domain atoms : Finset α)
    (hw : DisjointOn weight domain) (hs : atoms ⊆ domain) (input : β → A) :
    DisjointCircuit.supportSum input (interpret weight atoms) =
      DisjointCircuit.supportSum (fun a => DisjointCircuit.supportSum input (weight a)) atoms :=
  sum_interpret weight domain atoms hw hs input

end Values
end IntegerMultBounds.Networks.SupportInterpretation
