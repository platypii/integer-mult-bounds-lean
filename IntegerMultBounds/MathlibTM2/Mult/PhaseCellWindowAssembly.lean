module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface

/-! # Ordered publication of local solves

The schedule writes cores only. Its semantics is structural in the schedule,
so the same proof covers clipped and empty windows. Locality remains an explicit
premise about the ambient matrix; publication never introduces a volume factor.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface

variable {ι E : Type*} [DecidableEq ι]

/-- Publish in schedule order, retaining the initial value outside all cores. -/
def publishWindows (localOut : Window ι → ι → E) :
    List (Window ι) → (ι → E) → ι → E
  | [], out => out
  | w :: ws, out => publishWindows localOut ws
      (fun i => if i ∈ w.core then localOut w i else out i)

/-- Borrowed halo coordinates and spectators are unchanged unless owned by a core. -/
theorem publishWindows_preserves (localOut : Window ι → ι → E)
    (ws : List (Window ι)) (out : ι → E) (i : ι)
    (h : ∀ w ∈ ws, i ∉ w.core) :
    publishWindows localOut ws out i = out i := by
  induction ws generalizing out with
  | nil => rfl
  | cons w ws ih =>
    rw [publishWindows, ih _ (fun v hv => h v (List.mem_cons_of_mem w hv))]
    exact ite_eq_right (h w (List.mem_cons_self))

/-- Each covered coordinate is taken from one actual local result. -/
theorem publishWindows_source (localOut : Window ι → ι → E)
    (ws : List (Window ι)) (out : ι → E) (i : ι)
    (h : ∃ w ∈ ws, i ∈ w.core) :
    ∃ w ∈ ws, i ∈ w.core ∧ publishWindows localOut ws out i = localOut w i := by
  induction ws generalizing out with
  | nil => simp at h
  | cons w ws ih =>
    by_cases ht : ∃ v ∈ ws, i ∈ v.core
    · obtain ⟨v, hv, hi, he⟩ := ih
        (fun i => if i ∈ w.core then localOut w i else out i) ht
      exact ⟨v, List.mem_cons_of_mem w hv, hi, he⟩
    · have hw : i ∈ w.core := by
        obtain ⟨v, hv, hi⟩ := h
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hi
        · exact False.elim (ht ⟨v, hv, hi⟩)
      refine ⟨w, List.mem_cons_self, hw, ?_⟩
      rw [publishWindows, publishWindows_preserves]
      · exact ite_eq_left hw
      · intro v hv hi
        exact ht ⟨v, hv, hi⟩

/-- Assembly of halo solvers, with locality charged once at each coordinate. -/
theorem SolveSpec.of_published_halos [Fintype ι] (A : Matrix ι ι ℝ)
    (ws : List (Window ι)) (rhsBound arithmetic locality : ℝ)
    (solve : Window ι → (ι → ℝ) → ι → ℝ) (initial : (ι → ℝ) → ι → ℝ)
    (hcover : ∀ i, ∃ w ∈ ws, i ∈ w.core)
    (hsolve : ∀ w ∈ ws, SolveSpec A w.halo w.core rhsBound (solve w) arithmetic)
    (hlocal : ∀ w ∈ ws, ∀ x b,
      IntegerMultBounds.NLogN.SchurDominance.Solves A Finset.univ x b →
      (∀ i, |b i| ≤ rhsBound) →
      ∃ y, IntegerMultBounds.NLogN.SchurDominance.Solves A w.halo y b ∧
        ErrorOn w.core y x locality) :
    SolveSpec A Finset.univ Finset.univ rhsBound
      (fun b => publishWindows (fun w => solve w b) ws (initial b))
      (arithmetic + locality) := by
  intro x b hx hb i _
  obtain ⟨w, hw, hi, he⟩ := publishWindows_source
    (fun w => solve w b) ws (initial b) i (hcover i)
  change ‖publishWindows (fun w => solve w b) ws (initial b) i - x i‖ ≤ _
  rw [he]
  exact SolveSpec.with_locality A w rhsBound arithmetic locality (solve w)
    (hsolve w hw) (hlocal w hw) x b hx hb i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
