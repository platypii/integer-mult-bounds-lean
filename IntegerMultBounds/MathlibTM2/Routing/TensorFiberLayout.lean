module

public import IntegerMultBounds.MathlibTM2.Routing.RectangularHaloCoordinates

/-! Explicit prefix/coarse/spectator/local storage. A rectangular layout is
uniquely determined by its entries; later axis passes can name their exact data
rather than carrying a separate output-layout supplier. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.TensorFiberLayout
open RectangularHaloCoordinates
variable {E : Type}

def tabulate (P N B M : ℕ) (f : ℕ → ℕ → ℕ → ℕ → E) : List (List (List (List E))) :=
  (List.range P).map fun a => (List.range N).map fun k =>
    (List.range B).map fun b => (List.range M).map fun t => f a k b t

def Shape (P N B M : ℕ) (fibers : List (List (List (List E)))) : Prop :=
  fibers.length = P ∧ ∀ matrices ∈ fibers, matrices.length = N ∧
    ∀ rows ∈ matrices, rows.length = B ∧ ∀ row ∈ rows, row.length = M

theorem tabulate_shape (P N B M : ℕ) (f : ℕ → ℕ → ℕ → ℕ → E) :
    Shape P N B M (tabulate P N B M f) := by
  refine ⟨by simp [tabulate],?_⟩
  intro matrices hm
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hm
  refine ⟨by simp,?_⟩
  intro rows hr
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hr
  refine ⟨by simp,?_⟩
  intro row ht
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp ht
  simp

theorem tabulate_entry (fill : E) (P N B M : ℕ) (f : ℕ → ℕ → ℕ → ℕ → E)
    (a k b t : ℕ) (ha : a < P) (hk : k < N) (hb : b < B) (ht : t < M) :
    entry4 fill (tabulate P N B M f) a k b t = f a k b t := by
  simp [entry4,entry3,entry2,tabulate,ha,hk,hb,ht]

theorem eq_tabulate (fill : E) (P N B M : ℕ) (fibers : List (List (List (List E))))
    (f : ℕ → ℕ → ℕ → ℕ → E) (hshape : Shape P N B M fibers)
    (hentry : ∀ a < P, ∀ k < N, ∀ b < B, ∀ t < M, entry4 fill fibers a k b t = f a k b t) :
    fibers = tabulate P N B M f := by
  apply List.ext_getElem
  · simpa [tabulate] using hshape.1
  intro a ha ha'
  have hmat := hshape.2 fibers[a] (List.getElem_mem ha)
  have haP : a < P := lt_of_lt_of_eq ha hshape.1
  simp only [tabulate,List.getElem_map,List.getElem_range]
  apply List.ext_getElem
  · simpa using hmat.1
  intro k hk hk'
  have hrows := hmat.2 fibers[a][k] (List.getElem_mem hk)
  have hkN : k < N := lt_of_lt_of_eq hk hmat.1
  simp only [List.getElem_map,List.getElem_range]
  apply List.ext_getElem
  · simpa using hrows.1
  intro b hb hb'
  have hrow := hrows.2 fibers[a][k][b] (List.getElem_mem hb)
  have hbB : b < B := lt_of_lt_of_eq hb hrows.1
  simp only [List.getElem_map,List.getElem_range]
  apply List.ext_getElem
  · simpa using hrow
  intro t ht ht'
  have htM : t < M := lt_of_lt_of_eq ht hrow
  simp only [List.getElem_map,List.getElem_range]
  simpa only [entry4,entry3,entry2,List.getElem?_eq_getElem ha,Option.getD_some,
    List.getElem?_eq_getElem hk,List.getElem?_eq_getElem hb,List.getElem?_eq_getElem ht]
    using hentry a haP k hkN b hbB t htM

end IntegerMultBounds.MathlibTM2.Routing.TensorFiberLayout
