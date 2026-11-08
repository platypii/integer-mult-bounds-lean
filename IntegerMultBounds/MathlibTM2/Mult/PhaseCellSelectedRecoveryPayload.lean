module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRowSelection

/-! Replica-major C-selection output is exactly the existing principal
recovery input payload. No full source line is materialized by this identity. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

noncomputable def selectedRhsFields (s : ℕ) {t : ℕ} [NeZero s] (Fs : List (ZMod t → GaussianInt)) :
    List (ZMod s → GaussianInt) := Fs.map fun F j => F (rowIndex s t j)

def selectedWindowPayload {s t : ℕ} (A w a n origin span : ℕ) (Fs : List (ZMod t → GaussianInt)) :=
  Fs.flatMap fun F => (localRowOrigins s t a n origin w).flatMap
    (fun p => ((cstream A w (cyclicInterval origin span F)).drop p).take w)

theorem selectedWindowPayload_cyclic {s t : ℕ} [NeZero s] (A w a n origin span : ℕ)
    (Fs : List (ZMod t → GaussianInt))
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span) :
    selectedWindowPayload (s := s) A w a n origin span Fs =
      Fs.flatMap (fun F => cstream A w (cyclicInterval a n (fun j => F (rowIndex s t j)))) := by
  apply List.flatMap_congr
  intro F _
  exact cyclicRowOrigins_payload A w a n origin span F hwindow

theorem selectedWindowPayload_eq {s t : ℕ} [NeZero s] (A w a n origin span : ℕ)
    (Fs : List (ZMod t → GaussianInt)) (hsource : a+n ≤ s)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span) :
    selectedWindowPayload (s := s) A w a n origin span Fs =
      cstream A w ((selectedRhsFields s Fs).map (packedInterval a n)).flatten := by
  have hh : selectedWindowPayload (s := s) A w a n origin span Fs =
      Fs.flatMap (fun F => cstream A w (packedInterval a n (fun j => F (rowIndex s t j)))) := by
    apply List.flatMap_congr
    intro F hF
    rw [cyclicRowOrigins_payload A w a n origin span F hwindow,cyclicInterval_eq_packed _ hsource]
  rw [hh]
  simp only [selectedRhsFields,List.map_map,Function.comp_def,cstream,List.flatten_eq_flatMap,List.flatMap_assoc,id_eq,List.flatMap_map]

theorem selectedWindowPayload_length {s t : ℕ} [NeZero s] (A w a n origin span : ℕ)
    (Fs : List (ZMod t → GaussianInt)) (hsource : a+n ≤ s)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span) :
    (selectedWindowPayload (s := s) A w a n origin span Fs).length = Fs.length*n*w := by
  rw [selectedWindowPayload_eq A w a n origin span Fs hsource hwindow,length_cstream]
  have hh : ∀ F : ZMod s → GaussianInt, (packedInterval a n F).length = n :=
    fun F => packedInterval_length F hsource
  simp [selectedRhsFields,List.length_flatten,List.map_map,Function.comp_def,hh]

theorem selectedRhsFields_bounded {s t p : ℕ} [NeZero s] (Fs : List (ZMod t → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    ∀ F ∈ selectedRhsFields s Fs, ∀ i, ‖value p (F i)‖ ≤ 1 := by
  intro F hmem i
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hmem
  exact hF G hG _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
