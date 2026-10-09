import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedPlacedRun
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Erase four physically supplied shape outputs after their last use. Every
bit, sentinel and sequential join is charged; all other caller tapes are fixed. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedPlacedCleanup
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}

def cleared (caller : Tapes t a) (focus : Fin 4 → Fin t) :=
  setTape (setTape (setTape (setTape caller (focus 0) (fun _ => blank) 0)
    (focus 1) (fun _ => blank) 0) (focus 2) (fun _ => blank) 0) (focus 3) (fun _ => blank) 0

def program (focus : Fin 4 → Fin t) := seq (seq (seq
  (BinaryDescriptorCleanupList.oneProgram (a := a) (focus 0))
  (BinaryDescriptorCleanupList.oneProgram (a := a) (focus 1)))
  (BinaryDescriptorCleanupList.oneProgram (a := a) (focus 2)))
  (BinaryDescriptorCleanupList.oneProgram (a := a) (focus 3))

def cost (hs : Fin 4 → List Bool) :=
  2*((hs 0).length+(hs 1).length+(hs 2).length+(hs 3).length)+19

theorem cleans (caller : Tapes t a) (focus : Fin 4 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 4 → List Bool)
    (ht : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (focus i) = 1) :
    HoareTime (program (a := a) focus) (fun v => v = caller)
      (fun v => v = cleared caller focus) (cost hs) := by
  have hdesc (i : Fin 4) : caller.tape (focus i) = BinaryDescriptorStack.descriptor (hs i) := by
    rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
    exact ht i
  have h0 := BinaryDescriptorCleanupList.one_hoare (focus 0) caller (hs 0) (hdesc 0) (hh 0)
  have h1 := BinaryDescriptorCleanupList.one_hoare (focus 1)
    (setTape caller (focus 0) (fun _ => blank) 0) (hs 1)
    (by simpa [setTape,hf.eq_iff] using hdesc 1) (by simp [setTape,hf.eq_iff,hh])
  have h2 := BinaryDescriptorCleanupList.one_hoare (focus 2)
    (setTape (setTape caller (focus 0) (fun _ => blank) 0) (focus 1) (fun _ => blank) 0) (hs 2)
    (by simpa [setTape,hf.eq_iff] using hdesc 2) (by simp [setTape,hf.eq_iff,hh])
  have h3 := BinaryDescriptorCleanupList.one_hoare (focus 3)
    (setTape (setTape (setTape caller (focus 0) (fun _ => blank) 0)
      (focus 1) (fun _ => blank) 0) (focus 2) (fun _ => blank) 0) (hs 3)
    (by simpa [setTape,hf.eq_iff] using hdesc 3) (by simp [setTape,hf.eq_iff,hh])
  exact (((h0.seq h1).seq h2).seq h3).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)


theorem cleared_outputs (caller : Tapes t a) (focus : Fin 4 → Fin t) (hf : Function.Injective focus) :
    ∀ i, (cleared caller focus).tape (focus i) = (fun _ => blank) ∧
      (cleared caller focus).head (focus i) = 0 := by
  intro i
  fin_cases i <;> simp [cleared,setTape,hf.eq_iff]

theorem frame (caller : Tapes t a) (focus : Fin 4 → Fin t) (i : Fin t)
    (hi : ∀ j, i ≠ focus j) :
    (cleared caller focus).tape i = caller.tape i ∧
      (cleared caller focus).head i = caller.head i := by
  simp [cleared,setTape,hi]

theorem cost_bound (hs : Fin 4 → List Bool) (V : ℕ) (hV : 0 < V)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hv : ∀ i, Counter.value (hs i) ≤ V) :
    cost hs ≤ 35*V := by
  have h0 := CompactGadgetReservationHeadersCost.length_bound (hs 0) (hc 0) V (hv 0) hV
  have h1 := CompactGadgetReservationHeadersCost.length_bound (hs 1) (hc 1) V (hv 1) hV
  have h2 := CompactGadgetReservationHeadersCost.length_bound (hs 2) (hc 2) V (hv 2) hV
  have h3 := CompactGadgetReservationHeadersCost.length_bound (hs 3) (hc 3) V (hv 3) hV
  unfold cost
  omega


open CompactGadgetReservationShape
open CompactGadgetReservationHeadersCarvedData

theorem header_values_le (s : Shape) (rows w : ℕ) (f : Front)
    (hr : 0 < rows) (hp : 0 < s.payload) (hw : w ≤ s.H) :
    ∀ i, Counter.value (CompactGadgetReservationHeadersCarvedRouting.headerWords s rows w f i) ≤ rows*s.recordWidth := by
  have he := bits_decomposition s w hw f
  have hrec : s.recordWidth ≤ rows*s.recordWidth := Nat.le_mul_of_pos_left _ hr
  have hpow : 2^s.bits ≤ rows*s.recordWidth := (Nat.le_mul_of_pos_right _ hp).trans hrec
  have hpre : s.prefixRange rows f ≤ rows*s.recordWidth := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : s.prefixBits f ≤ s.bits)
    have hpw := Nat.le_mul_of_pos_right (2^s.bits) hp
    unfold Shape.prefixRange Shape.recordWidth
    nlinarith
  have hgap : gap s w f ≤ rows*s.recordWidth := by
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : gapBits s w f ≤ s.bits)).trans hpow
  have hsuf : suffix s w ≤ rows*s.recordWidth := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : afterBits s w ≤ s.bits)
    exact (Nat.mul_le_mul_right s.payload h).trans hrec
  have hwidth := CompactGadgetReservationHeadersCarvedPlacedRun.width_volume s rows w hr hp hw
  intro i
  rw [CompactGadgetReservationHeadersCarvedRouting.header_values]
  fin_cases i <;> simp only [BinaryRadixRangePrepare.values]
  · exact hpre
  · exact hgap
  · exact hsuf
  · exact hwidth

theorem carved_cost_bound (s : Shape) (rows w : ℕ) (f : Front)
    (hr : 0 < rows) (hp : 0 < s.payload) (hw : w ≤ s.H) :
    cost (CompactGadgetReservationHeadersCarvedRouting.headerWords s rows w f) ≤ 35*(rows*s.recordWidth) :=
  cost_bound _ _ (by unfold Shape.recordWidth; positivity)
    (CompactGadgetReservationHeadersCarvedRouting.header_canonical s rows w f)
    (header_values_le s rows w f hr hp hw)

theorem cleans_result (caller : Tapes t a) (focus : Fin 12 → Fin t) (hf : Function.Injective focus)
    (s : Shape) (rows w : ℕ) (f : Front) :
    HoareTime (program (a := a) (CompactGadgetReservationHeadersCarvedPlacedRun.outputFocus focus))
      (fun v => v = CompactGadgetReservationHeadersCarvedPlacedRun.result caller focus s rows w f)
      (fun v => v = cleared (CompactGadgetReservationHeadersCarvedPlacedRun.result caller focus s rows w f)
        (CompactGadgetReservationHeadersCarvedPlacedRun.outputFocus focus))
      (cost (CompactGadgetReservationHeadersCarvedRouting.headerWords s rows w f)) :=
  cleans _ _ (CompactGadgetReservationHeadersCarvedPlacedRun.output_injective focus hf) _
    (CompactGadgetReservationHeadersCarvedPlacedRun.result_headers caller focus hf s rows w f).1
    (CompactGadgetReservationHeadersCarvedPlacedRun.result_headers caller focus hf s rows w f).2

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedPlacedCleanup
