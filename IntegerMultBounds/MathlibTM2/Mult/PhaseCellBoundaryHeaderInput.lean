module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamLoadedReady

/-! Ordinary retained boundary scalars and blank destinations, before the
physical control bank is loaded. The two changing data ports are not inputs. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {A s : ℕ}

structure BoundaryHeaderInput (p width W D N : ℕ) (masters : Fin 11 → Fin 117)
    (seedValue : Fin 117 → ℕ) (S : Stacks 117 A) : Prop where
  separated : ∀ i, ∀ k ∈ List.ofFn boundarySeamMasterRole++[27,28], masters i ≠ k
  dataOff : ∀ i, masters i ≠ 95 ∧ masters i ≠ 96
  words : BoundarySeamHeaderWords (s := s) p width W D N seedValue (fun i => S.R (masters i))
  blank : ∀ i, i.val < 63 → i ≠ 95 → i ≠ 96 → S.R i = []

theorem BoundaryHeaderInput.of_frame (p width W D N : ℕ) (masters : Fin 11 → Fin 117)
    (seedValue : Fin 117 → ℕ) (S F : Stacks 117 A)
    (h : BoundaryHeaderInput (s := s) p width W D N masters seedValue S)
    (hread : ∀ i, i ≠ 95 → i ≠ 96 → F.R i = S.R i) :
    BoundaryHeaderInput (s := s) p width W D N masters seedValue F := by
  refine ⟨h.separated,h.dataOff,?_,?_⟩
  · have hm : (fun i => F.R (masters i)) = (fun i => S.R (masters i)) :=
      funext (fun i => hread _ (h.dataOff i).1 (h.dataOff i).2)
    rw [hm]
    exact h.words
  · intro i hi hs hd
    rw [hread i hs hd]
    exact h.blank i hi hs hd

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
