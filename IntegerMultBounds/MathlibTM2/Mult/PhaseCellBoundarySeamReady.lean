module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySlotSeamPublication

/-! Persistent control facts are independent of the changing archive ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A s : ℕ}

structure BoundarySeamReady (p width W D N : ℕ) (cropCount : Fin 3 → Fin 117)
    (seedValue : Fin 117 → ℕ) (S : Stacks 117 A) : Prop where
  cropOff : ∀ slot, cropCount slot ≠ 95 ∧ cropCount slot ≠ 96
  widthRuler : (S.R 58).length = D
  zero : S.R 59 = []
  words : ∀ j, S.R (boundarySeedGlobals j) = binSyms D (seedValue (boundarySeedGlobals j))
  tableBlank : ∀ r, S.R (boundaryCounterRegister r) = []
  masters : S.R 26 = [] ∧ S.R 24 = [] ∧ S.R 54 = [] ∧ S.R 19 = []
  bits : ∀ slot, (S.R (cropCount slot)).length =
    coreLength s width (boundaryCropIndex s width slot)*(2*p+13)
  fresh : ∀ i ∈ standardSeamPublicationPlan.support,
    i ≠ standardSeamPublicationPlan.advances → S.R i = []
  setupTmp : S.R 27 = []
  setupSaved : S.R 28 = []
  retireTmp : S.R 29 = []
  wide : (S.R 17).length = W
  word : (S.R 18).length = 2*p+13
  clock : (S.R 15).length = N
  line : (S.R 16).length = s
  blank : ∀ i ∈ [(20:Fin 117),21,22,23], S.R i = []

theorem BoundarySeamReady.of_frame (p width W D N : ℕ) (cropCount : Fin 3 → Fin 117)
    (seedValue : Fin 117 → ℕ) (S M : Stacks 117 A)
    (h : BoundarySeamReady (s := s) p width W D N cropCount seedValue S)
    (hread : ∀ i, i ≠ 95 → i ≠ 96 → M.R i = S.R i) :
    BoundarySeamReady (s := s) p width W D N cropCount seedValue M := by
  have hsmall (i : Fin 117) (hi : i.val < 60) : M.R i = S.R i := by
    apply hread i <;> intro he <;> have hv := congrArg Fin.val he <;> simp at hv <;> omega
  refine ⟨h.cropOff,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hsmall 58 (by decide)] using h.widthRuler
  · simpa only [hsmall 59 (by decide)] using h.zero
  · intro j
    rw [hsmall (boundarySeedGlobals j) (by fin_cases j <;> decide)]
    exact h.words j
  · intro r
    rw [hsmall (boundaryCounterRegister r) ((boundaryCounterRegister_bounds r).2.trans_le (by decide))]
    exact h.tableBlank r
  · simpa only [hsmall 26 (by decide),hsmall 24 (by decide),hsmall 54 (by decide),
      hsmall 19 (by decide)] using h.masters
  · intro slot
    rw [hread _ (h.cropOff slot).1 (h.cropOff slot).2]
    exact h.bits slot
  · intro i hi hne
    have hs : ∀ i ∈ standardSeamPublicationPlan.support, i.val < 60 := by decide +kernel
    rw [hsmall i (hs i hi)]
    exact h.fresh i hi hne
  · simpa only [hsmall 27 (by decide)] using h.setupTmp
  · simpa only [hsmall 28 (by decide)] using h.setupSaved
  · simpa only [hsmall 29 (by decide)] using h.retireTmp
  · simpa only [hsmall 17 (by decide)] using h.wide
  · simpa only [hsmall 18 (by decide)] using h.word
  · simpa only [hsmall 15 (by decide)] using h.clock
  · simpa only [hsmall 16 (by decide)] using h.line
  · intro i hi
    have hs : ∀ i ∈ [(20:Fin 117),21,22,23], i.val < 60 := by decide +kernel
    rw [hsmall i (hs i hi)]
    exact h.blank i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
