module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBatchState
public import IntegerMultBounds.MathlibTM2.Mult.ChirpS1DimensionFrame

/-! # Shared chirp workspace separated from generated unary dimensions -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.MathlibTM2.Fast

def chirpBatchEmpty {T : ℕ} (j : SetupReg → Fin T) (rg : RpReg → Fin T)
    (e : CorrelationReg → Fin T) (recordSaved saved acc buf savedBlock tmp : Fin T) : List (Fin T) :=
  ((setupWritten ++ setupScratch).map j) ++ [recordSaved, saved, acc, buf, savedBlock, tmp] ++
    ([RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d1, .d2, .d3, .out].map rg) ++
    ([CorrelationReg.triples, .skip, .recordSymbols, .batchSaved, .acc, .savedSource,
      .savedSkip, .recordSaved, .current, .saved, .buf, .tmp].map e)

def chirpBatchDimensions {T : ℕ} (j : SetupReg → Fin T) (records : Fin T)
    (e : CorrelationReg → Fin T) : Fin 7 → Fin T :=
  ![j .p, j .l, j .w, j .a, j .b, records, e .m]

/-- Empty scratch and the ring bank's left-stack/private-stack frame, with no unary inputs. -/
structure ChirpBatchWorkspace {T A : ℕ} (j : SetupReg → Fin T) (rg : RpReg → Fin T)
    (ι : Fin 91 → Fin T) (e : CorrelationReg → Fin T)
    (recordSaved saved acc buf savedBlock tmp : Fin T) (S : Stacks T A) : Prop where
  clean : RpClean ι S
  empty : ∀ k ∈ chirpBatchEmpty j rg e recordSaved saved acc buf savedBlock tmp, S.R k = []

/-- Exact generated dimensions plus scratch emptiness imply the existing caller contract. -/
theorem ChirpBatchWorkspace.toState {T A : ℕ}
    {j : SetupReg → Fin T} {rg : RpReg → Fin T} {ι : Fin 91 → Fin T} {e : CorrelationReg → Fin T}
    {records recordSaved saved acc buf savedBlock tmp : Fin T} {q t m w l : ℕ} {S : Stacks T A}
    (h : ChirpBatchWorkspace j rg ι e recordSaved saved acc buf savedBlock tmp S)
    (hdim : ∀ i, (S.R (chirpBatchDimensions j records e i)).length = chirpS1DimensionCount q t m w l i) :
    ChirpBatchState j rg ι e records recordSaved saved acc buf savedBlock tmp q l w
      (chirpBlockCount t m) m S := by
  refine ⟨h.clean, hdim 0, hdim 1, hdim 2, hdim 3, hdim 4, ?_, hdim 5, ?_, ?_, hdim 6, ?_, ?_, ?_⟩
  · intro r hr
    exact h.empty _ (by simp only [chirpBatchEmpty, List.mem_append]; exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨r, hr, rfl⟩))))
  · intro k hk
    exact h.empty k (by simp only [chirpBatchEmpty, List.mem_append]; exact Or.inl (Or.inl (Or.inr hk)))
  · intro r hr
    apply h.empty
    simp only [chirpBatchEmpty, List.mem_append]
    exact Or.inl (Or.inr (List.mem_map.mpr ⟨r, by simpa using List.mem_append_left [.out] hr, rfl⟩))
  · apply h.empty
    simp [chirpBatchEmpty]
  · intro r hr
    apply h.empty
    simp only [chirpBatchEmpty, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨r, List.mem_append_left _ hr, rfl⟩)
  · intro r hr
    apply h.empty
    simp only [chirpBatchEmpty, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨r, List.mem_append_right [CorrelationReg.triples, .skip, .recordSymbols] hr, rfl⟩)

/-- An operand write outside scratch and the private bank preserves workspace emptiness. -/
theorem ChirpBatchWorkspace.update_operand {T A : ℕ}
    {j : SetupReg → Fin T} {rg : RpReg → Fin T} {ι : Fin 91 → Fin T} {e : CorrelationReg → Fin T}
    {recordSaved saved acc buf savedBlock tmp : Fin T} {S : Stacks T A}
    (h : ChirpBatchWorkspace j rg ι e recordSaved saved acc buf savedBlock tmp S)
    (src : Fin T) (words : List (Fin (A + 4)))
    (hempty : ∀ k ∈ chirpBatchEmpty j rg e recordSaved saved acc buf savedBlock tmp, k ≠ src)
    (hprivate : ∀ r : Fin 91, 4 ≤ r.val → ι r ≠ src) :
    ChirpBatchWorkspace j rg ι e recordSaved saved acc buf savedBlock tmp
      { S with R := Function.update S.R src words } := by
  constructor
  · exact ⟨h.clean.1, fun r hr => (Function.update_of_ne (hprivate r hr) _ _).trans (h.clean.2 r hr)⟩
  · intro k hk
    exact (Function.update_of_ne (hempty k hk) _ _).trans (h.empty k hk)

/-- Installing the seven dimensions preserves all scratch preconditions and closes readiness. -/
theorem ChirpBatchWorkspace.install {T A : ℕ}
    {j : SetupReg → Fin T} {rg : RpReg → Fin T} {ι : Fin 91 → Fin T} {e : CorrelationReg → Fin T}
    {records recordSaved saved acc buf savedBlock tmp : Fin T} {q t m w l : ℕ} {S : Stacks T A}
    (h : ChirpBatchWorkspace j rg ι e recordSaved saved acc buf savedBlock tmp S)
    (hinj : Function.Injective (chirpBatchDimensions j records e))
    (hblank : ∀ i, S.R (chirpBatchDimensions j records e i) = [])
    (hsep : ∀ k ∈ chirpBatchEmpty j rg e recordSaved saved acc buf savedBlock tmp,
      ∀ i, k ≠ chirpBatchDimensions j records e i)
    (hprivate : ∀ r : Fin 91, 4 ≤ r.val → ∀ i, ι r ≠ chirpBatchDimensions j records e i) :
    ChirpBatchState j rg ι e records recordSaved saved acc buf savedBlock tmp q l w
      (chirpBlockCount t m) m
      { S with R := (unaryCopiesR (chirpS1DimensionValues q t m w l) S.R
          (chirpS1Assignments (chirpBatchDimensions j records e))) } := by
  apply ChirpBatchWorkspace.toState
  · constructor
    · exact ⟨h.clean.1, fun r hr =>
        (chirpS1Dimensions_off _ q t m w l S.R (ι r) (hprivate r hr)).trans (h.clean.2 r hr)⟩
    · intro k hk
      exact (chirpS1Dimensions_off _ q t m w l S.R k (hsep k hk)).trans (h.empty k hk)
  · intro i
    have hi := chirpS1Dimensions_at (chirpBatchDimensions j records e) hinj q t m w l S.R i
    rw [hblank, List.append_nil] at hi
    exact congrArg List.length hi |>.trans (List.length_replicate ..)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
