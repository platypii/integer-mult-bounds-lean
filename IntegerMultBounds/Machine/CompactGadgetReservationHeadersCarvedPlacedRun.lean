import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedPlacedWidth

/-! Physical shape synthesis from original caller descriptors. Caller ports
0..6 are chunk, axes, global guard, n, active, rows, payload; 7..10 are initially
blank width/P/G/B outputs; port 11 is the retained original packing factor.
The product and complete carved schedule reuse one blank forty-tape bank. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedPlacedRun
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationHeadersCarvedData
open CompactGadgetReservationHeadersCarvedSchedule
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {t a : ℕ}

def headerFocus (focus : Fin 12 → Fin t) : Fin 11 → Fin t := focus ∘ Fin.castAdd 1
def widthFocus (focus : Fin 12 → Fin t) : Fin 3 → Fin t := fun i => focus (![11,3,7] i)
theorem header_injective (focus : Fin 12 → Fin t) (hf : Function.Injective focus) :
    Function.Injective (headerFocus focus) := hf.comp (Fin.castAdd_injective _ _)
theorem width_injective (focus : Fin 12 → Fin t) (hf : Function.Injective focus) :
    Function.Injective (widthFocus focus) := hf.comp (by decide : Function.Injective (![11,3,7] : Fin 3 → Fin 12))

def sources (hs : Fin 7 → List Bool) : Tapes 11 a :=
  setTape (CompactGadgetReservationHeadersCarvedPlaced.sources hs 0) 7 (fun _ => blank) 0

def installed (caller : Tapes t a) (focus : Fin 12 → Fin t) (w : ℕ) :=
  setTape caller (focus 7) (RadixZeroFill.encodedBinary (bits w)) 1
def result (caller : Tapes t a) (focus : Fin 12 → Fin t) (s : Shape) (rows w : ℕ) (f : Front) :=
  CompactGadgetReservationHeadersCarvedPlaced.result (installed caller focus w) (headerFocus focus) s rows w f


def outputFocus (focus : Fin 12 → Fin t) : Fin 4 → Fin t := fun i => focus (![8,9,10,7] i)
theorem output_injective (focus : Fin 12 → Fin t) (hf : Function.Injective focus) :
    Function.Injective (outputFocus focus) := hf.comp (by decide : Function.Injective (![8,9,10,7] : Fin 4 → Fin 12))

theorem result_headers (caller : Tapes t a) (focus : Fin 12 → Fin t) (hf : Function.Injective focus)
    (s : Shape) (rows w : ℕ) (f : Front) :
    (∀ i, (result caller focus s rows w f).tape (outputFocus focus i) =
      RadixZeroFill.encodedBinary (CompactGadgetReservationHeadersCarvedRouting.headerWords s rows w f i)) ∧
    (∀ i, (result caller focus s rows w f).head (outputFocus focus i) = 1) := by
  constructor <;> intro i <;> fin_cases i
  all_goals simp [result,installed,outputFocus,headerFocus,
    CompactGadgetReservationHeadersCarvedPlaced.result,setTape,hf.eq_iff,
    CompactGadgetReservationHeadersCarvedRouting.headerWords,BinaryRadixRangePrepare.values]

def program (focus : Fin 12 → Fin t) (hf : Function.Injective focus) (f : Front) := seq
  (CompactGadgetReservationHeadersCarvedPlacedWidth.program (a := a) (widthFocus focus) (width_injective focus hf))
  (CompactGadgetReservationHeadersCarvedPlaced.program (a := a) (headerFocus focus) (header_injective focus hf) f)

def cost (hs : Fin 7 → List Bool) (w : ℕ) (f : Front) :=
  (53*w+28)+1+CompactGadgetReservationHeadersOps.bound (schedule f) (initial hs w)

theorem sources_install (hs : Fin 7 → List Bool) (w : ℕ) :
    setTape (sources (a := a) hs) 7 (RadixZeroFill.encodedBinary (bits w)) 1 =
      CompactGadgetReservationHeadersCarvedPlaced.sources hs w := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [sources,SharedBank.payload,CompactGadgetReservationHeadersCarvedPlaced.sources,
    setTape,CompactGadgetReservationHeadersCarvedPlaced.ports,
    CompactGadgetReservationHeadersWords.bank,CompactGadgetReservationHeadersCore.bank,
    CleanSubbank.bank,CompactGadgetReservationHeadersWords.common,
    CompactGadgetReservationHeadersWords.head,CompactGadgetReservationHeadersWords.tape,
    initial,CompactGadgetReservationHeadersSchedule.initial,Tapes.append,Fin.addCases]

theorem constructs (caller : Tapes t a) (focus : Fin 12 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 7 → List Bool) (ws : List Bool) (s : Shape) (n rows b : ℕ) (f : Front)
    (hsrc : SharedBank.payload caller (headerFocus focus) = sources hs)
    (ht : caller.tape (focus 11) = RadixZeroFill.encodedBinary ws) (hh : caller.head (focus 11) = 1)
    (hv : ∀ i, Counter.value (hs i) = originalValues s n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hvb : Counter.value ws = b) (hcb : GrowingCounterData.Canonical ws) (hb : 0 < b)
    (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard) (hw : n*b ≤ s.H) :
    HoareTime (program (a := a) focus hf f)
      (fun v => v = CleanSubbank.bank (s := 40) caller)
      (fun v => v = CleanSubbank.bank (s := 40) (result caller focus s rows (n*b) f))
      (cost hs (n*b) f) := by
  have htn := congrFun (congrArg Tapes.tape hsrc) 3
  have hhn := congrFun (congrArg Tapes.head hsrc) 3
  have htw := congrFun (congrArg Tapes.tape hsrc) 7
  have hhw := congrFun (congrArg Tapes.head hsrc) 7
  simp only [SharedBank.payload,headerFocus,Function.comp_apply] at htn hhn htw hhw
  have hnval : Counter.value (hs 3) = n := by simpa [originalValues] using hv 3
  have hprod := CompactGadgetReservationHeadersCarvedPlacedWidth.constructs caller (widthFocus focus)
    (width_injective focus hf) ws (hs 3) n b hb hvb hnval hcb (hc 3) ht hh
    (by simpa [widthFocus,sources,SharedBank.payload,CompactGadgetReservationHeadersCarvedPlaced.sources,
      CompactGadgetReservationHeadersCarvedPlaced.ports,CompactGadgetReservationHeadersWords.bank,
      CompactGadgetReservationHeadersCore.bank,CleanSubbank.bank,CompactGadgetReservationHeadersWords.common,
      CompactGadgetReservationHeadersWords.tape,initial,CompactGadgetReservationHeadersSchedule.initial,
      Tapes.append,Fin.addCases,setTape] using htn)
    (by simpa [widthFocus,sources,SharedBank.payload,CompactGadgetReservationHeadersCarvedPlaced.sources,
      CompactGadgetReservationHeadersCarvedPlaced.ports,CompactGadgetReservationHeadersWords.bank,
      CompactGadgetReservationHeadersCore.bank,CleanSubbank.bank,CompactGadgetReservationHeadersWords.common,
      CompactGadgetReservationHeadersWords.head,initial,CompactGadgetReservationHeadersSchedule.initial,
      Tapes.append,Fin.addCases,setTape] using hhn)
    (by simpa [widthFocus,sources,setTape] using htw)
    (by simpa [widthFocus,sources,setTape] using hhw)
  have hready : SharedBank.payload (installed caller focus (n*b)) (headerFocus focus) =
      CompactGadgetReservationHeadersCarvedPlaced.sources hs (n*b) := by
    change SharedBank.payload (setTape caller (headerFocus focus 7) _ _) _ = _
    rw [CompactGadgetReservationPlacement.payload_set _ _ (header_injective focus hf),hsrc,sources_install]
  exact hprod.seq (CompactGadgetReservationHeadersCarvedPlaced.constructs
    (installed caller focus (n*b)) (headerFocus focus) (header_injective focus hf)
    hs s n rows (n*b) f hready hv hc hK hd hG hw)


theorem width_volume (s : Shape) (rows w : ℕ) (hr : 0 < rows) (hp : 0 < s.payload)
    (hw : w ≤ s.H) : w ≤ rows*s.recordWidth := by
  have hbits : w ≤ s.bits := by unfold Shape.bits; omega
  have hpow := (Nat.lt_pow_self (n := s.bits) (by decide : 1 < 2)).le
  have hrec : 2^s.bits ≤ s.recordWidth := Nat.le_mul_of_pos_right _ hp
  have hV : s.recordWidth ≤ rows*s.recordWidth := Nat.le_mul_of_pos_left _ hr
  exact hbits.trans (hpow.trans (hrec.trans hV))

theorem cost_bound (hs : Fin 7 → List Bool) (s : Shape) (n rows w : ℕ) (f : Front)
    (hv : ∀ i, Counter.value (hs i) = originalValues s n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : 0 < rows) (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard)
    (hp : 0 < s.payload) (hw : w ≤ s.H) :
    cost hs w f ≤ (31*CompactGadgetReservationHeadersCost.coefficient+82)*(rows*s.recordWidth) := by
  have hsched := CompactGadgetReservationHeadersCarvedVolume.cost_bound hs s n rows w f hv hc hr hK hd hG hp hw
  have hwV := width_volume s rows w hr hp hw
  have hV : 0 < rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  unfold cost
  nlinarith

theorem constructs_volume (caller : Tapes t a) (focus : Fin 12 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 7 → List Bool) (ws : List Bool) (s : Shape) (n rows b : ℕ) (f : Front)
    (hsrc : SharedBank.payload caller (headerFocus focus) = sources hs)
    (ht : caller.tape (focus 11) = RadixZeroFill.encodedBinary ws) (hh : caller.head (focus 11) = 1)
    (hv : ∀ i, Counter.value (hs i) = originalValues s n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hvb : Counter.value ws = b) (hcb : GrowingCounterData.Canonical ws) (hb : 0 < b)
    (hr : 0 < rows) (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard)
    (hp : 0 < s.payload) (hw : n*b ≤ s.H) :
    HoareTime (program (a := a) focus hf f)
      (fun v => v = CleanSubbank.bank (s := 40) caller)
      (fun v => v = CleanSubbank.bank (s := 40) (result caller focus s rows (n*b) f))
      ((31*CompactGadgetReservationHeadersCost.coefficient+82)*(rows*s.recordWidth)) :=
  (constructs caller focus hf hs ws s n rows b f hsrc ht hh hv hc hvb hcb hb hK hd hG hw).consequence
    (fun _ h => h) (fun _ h => h) (cost_bound hs s n rows (n*b) f hv hc hr hK hd hG hp hw)

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedPlacedRun
